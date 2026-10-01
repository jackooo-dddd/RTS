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
Require Import prosa.implementation.refinements.refinements.
Require Import prosa.implementation.refinements.arrival_bound.
Require Import prosa.implementation.refinements.task.
Require Import prosa.implementation.refinements.arrival_curve.
Require Import prosa.implementation.refinements.EDF.nonpreemptive_sched.
Require Import prosa.implementation.refinements.EDF.preemptive_sched.
Require Import prosa.implementation.refinements.FP.nonpreemptive_sched.
Require Import prosa.implementation.refinements.FP.preemptive_sched.
Require Import prosa.implementation.refinements.arrival_curve_prefix.
Require Import prosa.implementation.refinements.fast_search_space_computation.
Require Import prosa.implementation.refinements.FP.fast_search_space.
Require Import prosa.implementation.refinements.EDF.fast_search_space.
Require Import prosa.implementation.refinements.FP.refinements.
Require Import prosa.implementation.refinements.EDF.refinements.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.bound_on_total_hep_workload". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.bound_on_total_hep_workload.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.bound_on_total_hep_workload". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.check_point_FP". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.check_point_FP.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.check_point_FP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.blocking_bound_NP". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.blocking_bound_NP.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.blocking_bound_NP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.check_point_NP". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.check_point_NP.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.check_point_NP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.Task". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.Task.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.Task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.Job". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.Job.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.Job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.correct_search_space". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.correct_search_space.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.correct_search_space". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_FP_h". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_FP_h.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_FP_h". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_FP". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_FP.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_FP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.task_search_space_emax_EDF_h". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.task_search_space_emax_EDF_h.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.task_search_space_emax_EDF_h". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.task_search_space_emax_EDF". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.task_search_space_emax_EDF.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.task_search_space_emax_EDF". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_EDF". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_EDF.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_EDF". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.EDF_ss_generalize_FP_ss". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.EDF_ss_generalize_FP_ss.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.EDF_ss_generalize_FP_ss". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.fast_search_space.search_space_subset_EDF". Abort.
Check @prosa.implementation.refinements.EDF.fast_search_space.search_space_subset_EDF.
Goal True. idtac "END|prosa.implementation.refinements.EDF.fast_search_space.search_space_subset_EDF". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.nonpreemptive_sched.Task". Abort.
Check @prosa.implementation.refinements.EDF.nonpreemptive_sched.Task.
Goal True. idtac "END|prosa.implementation.refinements.EDF.nonpreemptive_sched.Task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.nonpreemptive_sched.Job". Abort.
Check @prosa.implementation.refinements.EDF.nonpreemptive_sched.Job.
Goal True. idtac "END|prosa.implementation.refinements.EDF.nonpreemptive_sched.Job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.nonpreemptive_sched.basic_ready_instance". Abort.
Check @prosa.implementation.refinements.EDF.nonpreemptive_sched.basic_ready_instance.
Goal True. idtac "END|prosa.implementation.refinements.EDF.nonpreemptive_sched.basic_ready_instance". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.nonpreemptive_sched.sched". Abort.
Check @prosa.implementation.refinements.EDF.nonpreemptive_sched.sched.
Goal True. idtac "END|prosa.implementation.refinements.EDF.nonpreemptive_sched.sched". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_jobs_must_be_ready_to_execute". Abort.
Check @prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_valid". Abort.
Check @prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_valid.
Goal True. idtac "END|prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_valid". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_nonpreemptive_next". Abort.
Check @prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_nonpreemptive_next.
Goal True. idtac "END|prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_nonpreemptive_next". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_nonpreemptive". Abort.
Check @prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_nonpreemptive.
Goal True. idtac "END|prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_nonpreemptive". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.nonpreemptive_sched.respects_policy_at_preemption_point_edf_np". Abort.
Check @prosa.implementation.refinements.EDF.nonpreemptive_sched.respects_policy_at_preemption_point_edf_np.
Goal True. idtac "END|prosa.implementation.refinements.EDF.nonpreemptive_sched.respects_policy_at_preemption_point_edf_np". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.preemptive_sched.Task". Abort.
Check @prosa.implementation.refinements.EDF.preemptive_sched.Task.
Goal True. idtac "END|prosa.implementation.refinements.EDF.preemptive_sched.Task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.preemptive_sched.Job". Abort.
Check @prosa.implementation.refinements.EDF.preemptive_sched.Job.
Goal True. idtac "END|prosa.implementation.refinements.EDF.preemptive_sched.Job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.preemptive_sched.basic_ready_instance". Abort.
Check @prosa.implementation.refinements.EDF.preemptive_sched.basic_ready_instance.
Goal True. idtac "END|prosa.implementation.refinements.EDF.preemptive_sched.basic_ready_instance". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.preemptive_sched.sched". Abort.
Check @prosa.implementation.refinements.EDF.preemptive_sched.sched.
Goal True. idtac "END|prosa.implementation.refinements.EDF.preemptive_sched.sched". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.preemptive_sched.sched_valid". Abort.
Check @prosa.implementation.refinements.EDF.preemptive_sched.sched_valid.
Goal True. idtac "END|prosa.implementation.refinements.EDF.preemptive_sched.sched_valid". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.preemptive_sched.respects_policy_at_preemption_point_edf_fp". Abort.
Check @prosa.implementation.refinements.EDF.preemptive_sched.respects_policy_at_preemption_point_edf_fp.
Goal True. idtac "END|prosa.implementation.refinements.EDF.preemptive_sched.respects_policy_at_preemption_point_edf_fp". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.total_rbf_T". Abort.
Check @prosa.implementation.refinements.EDF.refinements.total_rbf_T.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.total_rbf_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.bound_on_total_hep_workload_T". Abort.
Check @prosa.implementation.refinements.EDF.refinements.bound_on_total_hep_workload_T.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.bound_on_total_hep_workload_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.check_point_FP_T". Abort.
Check @prosa.implementation.refinements.EDF.refinements.check_point_FP_T.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.check_point_FP_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.blocking_bound_NP_T". Abort.
Check @prosa.implementation.refinements.EDF.refinements.blocking_bound_NP_T.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.blocking_bound_NP_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.check_point_NP_T". Abort.
Check @prosa.implementation.refinements.EDF.refinements.check_point_NP_T.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.check_point_NP_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.valid_arrivals_T". Abort.
Check @prosa.implementation.refinements.EDF.refinements.valid_arrivals_T.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.valid_arrivals_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.iota_N". Abort.
Check @prosa.implementation.refinements.EDF.refinements.iota_N.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.iota_N". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.task_search_space_emax_EDF_h_N". Abort.
Check @prosa.implementation.refinements.EDF.refinements.task_search_space_emax_EDF_h_N.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.task_search_space_emax_EDF_h_N". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.task_search_space_emax_EDF_N". Abort.
Check @prosa.implementation.refinements.EDF.refinements.task_search_space_emax_EDF_N.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.task_search_space_emax_EDF_N". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.search_space_emax_EDF_N". Abort.
Check @prosa.implementation.refinements.EDF.refinements.search_space_emax_EDF_N.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.search_space_emax_EDF_N". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.refine_task_search_space_emax_EDF". Abort.
Check @prosa.implementation.refinements.EDF.refinements.refine_task_search_space_emax_EDF.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.refine_task_search_space_emax_EDF". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.refine_search_space_emax_EDF". Abort.
Check @prosa.implementation.refinements.EDF.refinements.refine_search_space_emax_EDF.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.refine_search_space_emax_EDF". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.refine_total_rbf'". Abort.
Check @prosa.implementation.refinements.EDF.refinements.refine_total_rbf'.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.refine_total_rbf'". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.eq_listN". Abort.
Check @prosa.implementation.refinements.EDF.refinements.eq_listN.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.eq_listN". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.eq_NlistNN". Abort.
Check @prosa.implementation.refinements.EDF.refinements.eq_NlistNN.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.eq_NlistNN". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.eq_taskab". Abort.
Check @prosa.implementation.refinements.EDF.refinements.eq_taskab.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.eq_taskab". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.eq_task". Abort.
Check @prosa.implementation.refinements.EDF.refinements.eq_task.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.eq_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.refine_bound_on_total_hep_workload". Abort.
Check @prosa.implementation.refinements.EDF.refinements.refine_bound_on_total_hep_workload.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.refine_bound_on_total_hep_workload". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.refine_check_point_FP". Abort.
Check @prosa.implementation.refinements.EDF.refinements.refine_check_point_FP.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.refine_check_point_FP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.refine_check_point_FP'". Abort.
Check @prosa.implementation.refinements.EDF.refinements.refine_check_point_FP'.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.refine_check_point_FP'". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.refine_blocking_bound". Abort.
Check @prosa.implementation.refinements.EDF.refinements.refine_blocking_bound.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.refine_blocking_bound". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.refine_check_point_NP". Abort.
Check @prosa.implementation.refinements.EDF.refinements.refine_check_point_NP.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.refine_check_point_NP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.EDF.refinements.refine_check_point_NP'". Abort.
Check @prosa.implementation.refinements.EDF.refinements.refine_check_point_NP'.
Goal True. idtac "END|prosa.implementation.refinements.EDF.refinements.refine_check_point_NP'". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.fast_search_space.ohep_task". Abort.
Check @prosa.implementation.refinements.FP.fast_search_space.ohep_task.
Goal True. idtac "END|prosa.implementation.refinements.FP.fast_search_space.ohep_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.fast_search_space.total_hep_rbf". Abort.
Check @prosa.implementation.refinements.FP.fast_search_space.total_hep_rbf.
Goal True. idtac "END|prosa.implementation.refinements.FP.fast_search_space.total_hep_rbf". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.fast_search_space.total_ohep_rbf". Abort.
Check @prosa.implementation.refinements.FP.fast_search_space.total_ohep_rbf.
Goal True. idtac "END|prosa.implementation.refinements.FP.fast_search_space.total_ohep_rbf". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.fast_search_space.check_point_FP". Abort.
Check @prosa.implementation.refinements.FP.fast_search_space.check_point_FP.
Goal True. idtac "END|prosa.implementation.refinements.FP.fast_search_space.check_point_FP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.fast_search_space.blocking_bound_NP". Abort.
Check @prosa.implementation.refinements.FP.fast_search_space.blocking_bound_NP.
Goal True. idtac "END|prosa.implementation.refinements.FP.fast_search_space.blocking_bound_NP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.fast_search_space.check_point_NP". Abort.
Check @prosa.implementation.refinements.FP.fast_search_space.check_point_NP.
Goal True. idtac "END|prosa.implementation.refinements.FP.fast_search_space.check_point_NP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.fast_search_space.correct_search_space". Abort.
Check @prosa.implementation.refinements.FP.fast_search_space.correct_search_space.
Goal True. idtac "END|prosa.implementation.refinements.FP.fast_search_space.correct_search_space". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.fast_search_space.search_space_emax_FP_h". Abort.
Check @prosa.implementation.refinements.FP.fast_search_space.search_space_emax_FP_h.
Goal True. idtac "END|prosa.implementation.refinements.FP.fast_search_space.search_space_emax_FP_h". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.fast_search_space.search_space_emax_FP". Abort.
Check @prosa.implementation.refinements.FP.fast_search_space.search_space_emax_FP.
Goal True. idtac "END|prosa.implementation.refinements.FP.fast_search_space.search_space_emax_FP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.fast_search_space.search_space_subset_FP". Abort.
Check @prosa.implementation.refinements.FP.fast_search_space.search_space_subset_FP.
Goal True. idtac "END|prosa.implementation.refinements.FP.fast_search_space.search_space_subset_FP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.nonpreemptive_sched.Task". Abort.
Check @prosa.implementation.refinements.FP.nonpreemptive_sched.Task.
Goal True. idtac "END|prosa.implementation.refinements.FP.nonpreemptive_sched.Task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.nonpreemptive_sched.Job". Abort.
Check @prosa.implementation.refinements.FP.nonpreemptive_sched.Job.
Goal True. idtac "END|prosa.implementation.refinements.FP.nonpreemptive_sched.Job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.nonpreemptive_sched.sequential_ready_instance". Abort.
Check @prosa.implementation.refinements.FP.nonpreemptive_sched.sequential_ready_instance.
Goal True. idtac "END|prosa.implementation.refinements.FP.nonpreemptive_sched.sequential_ready_instance". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.nonpreemptive_sched.sched". Abort.
Check @prosa.implementation.refinements.FP.nonpreemptive_sched.sched.
Goal True. idtac "END|prosa.implementation.refinements.FP.nonpreemptive_sched.sched". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.nonpreemptive_sched.sched_jobs_must_be_ready_to_execute". Abort.
Check @prosa.implementation.refinements.FP.nonpreemptive_sched.sched_jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.implementation.refinements.FP.nonpreemptive_sched.sched_jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.nonpreemptive_sched.sched_valid". Abort.
Check @prosa.implementation.refinements.FP.nonpreemptive_sched.sched_valid.
Goal True. idtac "END|prosa.implementation.refinements.FP.nonpreemptive_sched.sched_valid". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.nonpreemptive_sched.sched_nonpreemptive_next". Abort.
Check @prosa.implementation.refinements.FP.nonpreemptive_sched.sched_nonpreemptive_next.
Goal True. idtac "END|prosa.implementation.refinements.FP.nonpreemptive_sched.sched_nonpreemptive_next". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.nonpreemptive_sched.sched_nonpreemptive". Abort.
Check @prosa.implementation.refinements.FP.nonpreemptive_sched.sched_nonpreemptive.
Goal True. idtac "END|prosa.implementation.refinements.FP.nonpreemptive_sched.sched_nonpreemptive". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.nonpreemptive_sched.respects_policy_at_preemption_point_np". Abort.
Check @prosa.implementation.refinements.FP.nonpreemptive_sched.respects_policy_at_preemption_point_np.
Goal True. idtac "END|prosa.implementation.refinements.FP.nonpreemptive_sched.respects_policy_at_preemption_point_np". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.preemptive_sched.Task". Abort.
Check @prosa.implementation.refinements.FP.preemptive_sched.Task.
Goal True. idtac "END|prosa.implementation.refinements.FP.preemptive_sched.Task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.preemptive_sched.Job". Abort.
Check @prosa.implementation.refinements.FP.preemptive_sched.Job.
Goal True. idtac "END|prosa.implementation.refinements.FP.preemptive_sched.Job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.preemptive_sched.sequential_ready_instance". Abort.
Check @prosa.implementation.refinements.FP.preemptive_sched.sequential_ready_instance.
Goal True. idtac "END|prosa.implementation.refinements.FP.preemptive_sched.sequential_ready_instance". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.preemptive_sched.sched". Abort.
Check @prosa.implementation.refinements.FP.preemptive_sched.sched.
Goal True. idtac "END|prosa.implementation.refinements.FP.preemptive_sched.sched". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.preemptive_sched.sched_valid". Abort.
Check @prosa.implementation.refinements.FP.preemptive_sched.sched_valid.
Goal True. idtac "END|prosa.implementation.refinements.FP.preemptive_sched.sched_valid". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.preemptive_sched.respects_policy_at_preemption_point". Abort.
Check @prosa.implementation.refinements.FP.preemptive_sched.respects_policy_at_preemption_point.
Goal True. idtac "END|prosa.implementation.refinements.FP.preemptive_sched.respects_policy_at_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.hep_task_T". Abort.
Check @prosa.implementation.refinements.FP.refinements.hep_task_T.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.hep_task_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.total_hep_rbf_T". Abort.
Check @prosa.implementation.refinements.FP.refinements.total_hep_rbf_T.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.total_hep_rbf_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.ohep_task_T". Abort.
Check @prosa.implementation.refinements.FP.refinements.ohep_task_T.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.ohep_task_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.total_ohep_rbf_T". Abort.
Check @prosa.implementation.refinements.FP.refinements.total_ohep_rbf_T.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.total_ohep_rbf_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.check_point_FP_T". Abort.
Check @prosa.implementation.refinements.FP.refinements.check_point_FP_T.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.check_point_FP_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.blocking_bound_NP_T". Abort.
Check @prosa.implementation.refinements.FP.refinements.blocking_bound_NP_T.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.blocking_bound_NP_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.check_point_NP_T". Abort.
Check @prosa.implementation.refinements.FP.refinements.check_point_NP_T.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.check_point_NP_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.iota_N". Abort.
Check @prosa.implementation.refinements.FP.refinements.iota_N.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.iota_N". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.search_space_emax_FP_h_N". Abort.
Check @prosa.implementation.refinements.FP.refinements.search_space_emax_FP_h_N.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.search_space_emax_FP_h_N". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.search_space_emax_FP_N". Abort.
Check @prosa.implementation.refinements.FP.refinements.search_space_emax_FP_N.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.search_space_emax_FP_N". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_search_space_emax". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_search_space_emax.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_search_space_emax". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_hep_task". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_hep_task.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_hep_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_total_hep_rbf". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_total_hep_rbf.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_total_hep_rbf". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_total_hep_rbf'". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_total_hep_rbf'.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_total_hep_rbf'". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.eq_listN". Abort.
Check @prosa.implementation.refinements.FP.refinements.eq_listN.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.eq_listN". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.eq_listNN". Abort.
Check @prosa.implementation.refinements.FP.refinements.eq_listNN.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.eq_listNN". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.eq_NlistNN". Abort.
Check @prosa.implementation.refinements.FP.refinements.eq_NlistNN.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.eq_NlistNN". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.eq_taskab". Abort.
Check @prosa.implementation.refinements.FP.refinements.eq_taskab.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.eq_taskab". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.eq_task". Abort.
Check @prosa.implementation.refinements.FP.refinements.eq_task.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.eq_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_task_eqdef". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_task_eqdef.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_task_eqdef". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_ohep_task". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_ohep_task.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_ohep_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_total_ohep_rbf". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_total_ohep_rbf.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_total_ohep_rbf". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_check_point". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_check_point.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_check_point". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_check_point'". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_check_point'.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_check_point'". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_blocking_bound". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_blocking_bound.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_blocking_bound". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_blocking_bound'". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_blocking_bound'.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_blocking_bound'". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_check_point_NP". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_check_point_NP.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_check_point_NP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.FP.refinements.refine_check_point_NP'". Abort.
Check @prosa.implementation.refinements.FP.refinements.refine_check_point_NP'.
Goal True. idtac "END|prosa.implementation.refinements.FP.refinements.refine_check_point_NP'". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.task_arrivals_bound_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.task_arrivals_bound_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.task_arrivals_bound_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.taskab_eqdef_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.taskab_eqdef_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.taskab_eqdef_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.horizon_of_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.horizon_of_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.horizon_of_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.steps_of_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.steps_of_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.steps_of_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.time_steps_of_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.time_steps_of_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.time_steps_of_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.step_at_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.step_at_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.step_at_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.value_at_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.value_at_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.value_at_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.extrapolated_arrival_curve_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.extrapolated_arrival_curve_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.extrapolated_arrival_curve_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.ltn_steps_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.ltn_steps_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.ltn_steps_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.sorted_ltn_steps_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.sorted_ltn_steps_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.sorted_ltn_steps_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.leq_steps_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.leq_steps_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.leq_steps_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.positive_horizon_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.positive_horizon_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.positive_horizon_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.large_horizon_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.large_horizon_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.large_horizon_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.no_inf_arrivals_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.no_inf_arrivals_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.no_inf_arrivals_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.specified_bursts_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.specified_bursts_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.specified_bursts_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.valid_extrapolated_arrival_curve_T". Abort.
Check @prosa.implementation.refinements.arrival_bound.valid_extrapolated_arrival_curve_T.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.valid_extrapolated_arrival_curve_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.ACPrefixT_to_ACPrefix". Abort.
Check @prosa.implementation.refinements.arrival_bound.ACPrefixT_to_ACPrefix.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.ACPrefixT_to_ACPrefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.RArrivalCurvePrefix". Abort.
Check @prosa.implementation.refinements.arrival_bound.RArrivalCurvePrefix.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.RArrivalCurvePrefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.ACPrefix_to_ACPrefixT". Abort.
Check @prosa.implementation.refinements.arrival_bound.ACPrefix_to_ACPrefixT.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.ACPrefix_to_ACPrefixT". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.task_abT_to_task_ab". Abort.
Check @prosa.implementation.refinements.arrival_bound.task_abT_to_task_ab.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.task_abT_to_task_ab". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.Rtask_ab". Abort.
Check @prosa.implementation.refinements.arrival_bound.Rtask_ab.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.Rtask_ab". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.task_ab_to_task_abT". Abort.
Check @prosa.implementation.refinements.arrival_bound.task_ab_to_task_abT.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.task_ab_to_task_abT". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.leq_stepsT_is_transitive". Abort.
Check @prosa.implementation.refinements.arrival_bound.leq_stepsT_is_transitive.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.leq_stepsT_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.ltn_stepsT_is_transitive". Abort.
Check @prosa.implementation.refinements.arrival_bound.ltn_stepsT_is_transitive.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.ltn_stepsT_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.refine_leq_steps". Abort.
Check @prosa.implementation.refinements.arrival_bound.refine_leq_steps.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.refine_leq_steps". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.refine_ltn_steps". Abort.
Check @prosa.implementation.refinements.arrival_bound.refine_ltn_steps.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.refine_ltn_steps". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.refine_ltn_steps_sorted". Abort.
Check @prosa.implementation.refinements.arrival_bound.refine_ltn_steps_sorted.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.refine_ltn_steps_sorted". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.refine_leq_steps_sorted". Abort.
Check @prosa.implementation.refinements.arrival_bound.refine_leq_steps_sorted.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.refine_leq_steps_sorted". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.refine_value_at". Abort.
Check @prosa.implementation.refinements.arrival_bound.refine_value_at.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.refine_value_at". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.refine_get_time_steps". Abort.
Check @prosa.implementation.refinements.arrival_bound.refine_get_time_steps.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.refine_get_time_steps". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.refine_arrival_curve_prefix". Abort.
Check @prosa.implementation.refinements.arrival_bound.refine_arrival_curve_prefix.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.refine_arrival_curve_prefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.refine_ArrivalPrefix". Abort.
Check @prosa.implementation.refinements.arrival_bound.refine_ArrivalPrefix.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.refine_ArrivalPrefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.eq_listN". Abort.
Check @prosa.implementation.refinements.arrival_bound.eq_listN.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.eq_listN". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.eq_NlistNN". Abort.
Check @prosa.implementation.refinements.arrival_bound.eq_NlistNN.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.eq_NlistNN". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.eq_taskab". Abort.
Check @prosa.implementation.refinements.arrival_bound.eq_taskab.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.eq_taskab". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_bound.refine_task_ab_eq". Abort.
Check @prosa.implementation.refinements.arrival_bound.refine_task_ab_eq.
Goal True. idtac "END|prosa.implementation.refinements.arrival_bound.refine_task_ab_eq". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.get_horizon_of_task". Abort.
Check @prosa.implementation.refinements.arrival_curve.get_horizon_of_task.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.get_horizon_of_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.get_time_steps_of_task". Abort.
Check @prosa.implementation.refinements.arrival_curve.get_time_steps_of_task.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.get_time_steps_of_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.time_steps_with_offset". Abort.
Check @prosa.implementation.refinements.arrival_curve.time_steps_with_offset.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.time_steps_with_offset". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.repeat_steps_with_offset". Abort.
Check @prosa.implementation.refinements.arrival_curve.repeat_steps_with_offset.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.repeat_steps_with_offset". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.task_rbf". Abort.
Check @prosa.implementation.refinements.arrival_curve.task_rbf.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.task_rbf". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.valid_arrivals". Abort.
Check @prosa.implementation.refinements.arrival_curve.valid_arrivals.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.valid_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.is_periodic_arrivals". Abort.
Check @prosa.implementation.refinements.arrival_curve.is_periodic_arrivals.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.is_periodic_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.is_sporadic_arrivals". Abort.
Check @prosa.implementation.refinements.arrival_curve.is_sporadic_arrivals.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.is_sporadic_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.is_etamax_arrivals". Abort.
Check @prosa.implementation.refinements.arrival_curve.is_etamax_arrivals.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.is_etamax_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.has_valid_arrival_curve_prefix". Abort.
Check @prosa.implementation.refinements.arrival_curve.has_valid_arrival_curve_prefix.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.has_valid_arrival_curve_prefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.task_set_with_valid_arrivals". Abort.
Check @prosa.implementation.refinements.arrival_curve.task_set_with_valid_arrivals.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.task_set_with_valid_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.arrival_cases". Abort.
Check @prosa.implementation.refinements.arrival_curve.arrival_cases.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.arrival_cases". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.refine_valid_arrivals". Abort.
Check @prosa.implementation.refinements.arrival_curve.refine_valid_arrivals.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.refine_valid_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.refine_repeat_steps_with_offset". Abort.
Check @prosa.implementation.refinements.arrival_curve.refine_repeat_steps_with_offset.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.refine_repeat_steps_with_offset". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.refine_get_horizon_of_task". Abort.
Check @prosa.implementation.refinements.arrival_curve.refine_get_horizon_of_task.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.refine_get_horizon_of_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.refine_ConcreteMaxArrivals'". Abort.
Check @prosa.implementation.refinements.arrival_curve.refine_ConcreteMaxArrivals'.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.refine_ConcreteMaxArrivals'". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.refine_get_arrival_curve_prefix". Abort.
Check @prosa.implementation.refinements.arrival_curve.refine_get_arrival_curve_prefix.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.refine_get_arrival_curve_prefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.refine_get_arrival_curve_prefix'". Abort.
Check @prosa.implementation.refinements.arrival_curve.refine_get_arrival_curve_prefix'.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.refine_get_arrival_curve_prefix'". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.refine_sorted_leq_steps". Abort.
Check @prosa.implementation.refinements.arrival_curve.refine_sorted_leq_steps.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.refine_sorted_leq_steps". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve.refine_task_rbf". Abort.
Check @prosa.implementation.refinements.arrival_curve.refine_task_rbf.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve.refine_task_rbf". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve_prefix.has_valid_arrival_curve_prefix_tsk". Abort.
Check @prosa.implementation.refinements.arrival_curve_prefix.has_valid_arrival_curve_prefix_tsk.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve_prefix.has_valid_arrival_curve_prefix_tsk". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve_prefix.steps_are_positive_if_first_step_is_positive". Abort.
Check @prosa.implementation.refinements.arrival_curve_prefix.steps_are_positive_if_first_step_is_positive.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve_prefix.steps_are_positive_if_first_step_is_positive". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve_prefix.nonshifted_offsets_are_positive". Abort.
Check @prosa.implementation.refinements.arrival_curve_prefix.nonshifted_offsets_are_positive.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve_prefix.nonshifted_offsets_are_positive". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.arrival_curve_prefix.time_steps_sorted". Abort.
Check @prosa.implementation.refinements.arrival_curve_prefix.time_steps_sorted.
Goal True. idtac "END|prosa.implementation.refinements.arrival_curve_prefix.time_steps_sorted". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.fast_search_space_computation.search_space_arrival_curve_prefix_FP_h". Abort.
Check @prosa.implementation.refinements.fast_search_space_computation.search_space_arrival_curve_prefix_FP_h.
Goal True. idtac "END|prosa.implementation.refinements.fast_search_space_computation.search_space_arrival_curve_prefix_FP_h". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.fast_search_space_computation.search_space_arrival_curve_prefix_FP". Abort.
Check @prosa.implementation.refinements.fast_search_space_computation.search_space_arrival_curve_prefix_FP.
Goal True. idtac "END|prosa.implementation.refinements.fast_search_space_computation.search_space_arrival_curve_prefix_FP". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.fast_search_space_computation.steps_lt_horizon_last_eq_horizon". Abort.
Check @prosa.implementation.refinements.fast_search_space_computation.steps_lt_horizon_last_eq_horizon.
Goal True. idtac "END|prosa.implementation.refinements.fast_search_space_computation.steps_lt_horizon_last_eq_horizon". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.fast_search_space_computation.structure_of_correct_search_space". Abort.
Check @prosa.implementation.refinements.fast_search_space_computation.structure_of_correct_search_space.
Goal True. idtac "END|prosa.implementation.refinements.fast_search_space_computation.structure_of_correct_search_space". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.fast_search_space_computation.multiple_of_horizon_in_approx_ss". Abort.
Check @prosa.implementation.refinements.fast_search_space_computation.multiple_of_horizon_in_approx_ss.
Goal True. idtac "END|prosa.implementation.refinements.fast_search_space_computation.multiple_of_horizon_in_approx_ss". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.fast_search_space_computation.steps_in_approx_ss". Abort.
Check @prosa.implementation.refinements.fast_search_space_computation.steps_in_approx_ss.
Goal True. idtac "END|prosa.implementation.refinements.fast_search_space_computation.steps_in_approx_ss". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.fast_search_space_computation.constant_max_arrivals". Abort.
Check @prosa.implementation.refinements.fast_search_space_computation.constant_max_arrivals.
Goal True. idtac "END|prosa.implementation.refinements.fast_search_space_computation.constant_max_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.fast_search_space_computation.task_search_space_subset". Abort.
Check @prosa.implementation.refinements.fast_search_space_computation.task_search_space_subset.
Goal True. idtac "END|prosa.implementation.refinements.fast_search_space_computation.task_search_space_subset". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.m_b2n". Abort.
Check @prosa.implementation.refinements.refinements.m_b2n.
Goal True. idtac "END|prosa.implementation.refinements.refinements.m_b2n". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.m_n2b". Abort.
Check @prosa.implementation.refinements.refinements.m_n2b.
Goal True. idtac "END|prosa.implementation.refinements.refinements.m_n2b". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.tmap". Abort.
Check @prosa.implementation.refinements.refinements.tmap.
Goal True. idtac "END|prosa.implementation.refinements.refinements.tmap". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.tb2tn". Abort.
Check @prosa.implementation.refinements.refinements.tb2tn.
Goal True. idtac "END|prosa.implementation.refinements.refinements.tb2tn". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.tn2tb". Abort.
Check @prosa.implementation.refinements.refinements.tn2tb.
Goal True. idtac "END|prosa.implementation.refinements.refinements.tn2tb". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.m_tb2tn". Abort.
Check @prosa.implementation.refinements.refinements.m_tb2tn.
Goal True. idtac "END|prosa.implementation.refinements.refinements.m_tb2tn". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.m_tn2tb". Abort.
Check @prosa.implementation.refinements.refinements.m_tn2tb.
Goal True. idtac "END|prosa.implementation.refinements.refinements.m_tn2tb". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.predn_T". Abort.
Check @prosa.implementation.refinements.refinements.predn_T.
Goal True. idtac "END|prosa.implementation.refinements.refinements.predn_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.maxn_T". Abort.
Check @prosa.implementation.refinements.refinements.maxn_T.
Goal True. idtac "END|prosa.implementation.refinements.refinements.maxn_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.minn_T". Abort.
Check @prosa.implementation.refinements.refinements.minn_T.
Goal True. idtac "END|prosa.implementation.refinements.refinements.minn_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.dvdn_T". Abort.
Check @prosa.implementation.refinements.refinements.dvdn_T.
Goal True. idtac "END|prosa.implementation.refinements.refinements.dvdn_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.div_ceil_T". Abort.
Check @prosa.implementation.refinements.refinements.div_ceil_T.
Goal True. idtac "END|prosa.implementation.refinements.refinements.div_ceil_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_b2n". Abort.
Check @prosa.implementation.refinements.refinements.refine_b2n.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_b2n". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.Rnat_pred". Abort.
Check @prosa.implementation.refinements.refinements.Rnat_pred.
Goal True. idtac "END|prosa.implementation.refinements.refinements.Rnat_pred". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_dvdn". Abort.
Check @prosa.implementation.refinements.refinements.refine_dvdn.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_dvdn". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_div_ceil". Abort.
Check @prosa.implementation.refinements.refinements.refine_div_ceil.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_div_ceil". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_minn". Abort.
Check @prosa.implementation.refinements.refinements.refine_minn.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_minn". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_maxn". Abort.
Check @prosa.implementation.refinements.refinements.refine_maxn.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_maxn". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.posBinNatNotZero". Abort.
Check @prosa.implementation.refinements.refinements.posBinNatNotZero.
Goal True. idtac "END|prosa.implementation.refinements.refinements.posBinNatNotZero". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.eq_SnPos_to_nPred". Abort.
Check @prosa.implementation.refinements.refinements.eq_SnPos_to_nPred.
Goal True. idtac "END|prosa.implementation.refinements.refinements.eq_SnPos_to_nPred". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_ltn". Abort.
Check @prosa.implementation.refinements.refinements.refine_ltn.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_ltn". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.iota_T". Abort.
Check @prosa.implementation.refinements.refinements.iota_T.
Goal True. idtac "END|prosa.implementation.refinements.refinements.iota_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.size_T". Abort.
Check @prosa.implementation.refinements.refinements.size_T.
Goal True. idtac "END|prosa.implementation.refinements.refinements.size_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.shift_points_pos_T". Abort.
Check @prosa.implementation.refinements.refinements.shift_points_pos_T.
Goal True. idtac "END|prosa.implementation.refinements.refinements.shift_points_pos_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.shift_points_neg_T". Abort.
Check @prosa.implementation.refinements.refinements.shift_points_neg_T.
Goal True. idtac "END|prosa.implementation.refinements.refinements.shift_points_neg_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_map". Abort.
Check @prosa.implementation.refinements.refinements.refine_map.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_map". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_zip". Abort.
Check @prosa.implementation.refinements.refinements.refine_zip.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_zip". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_all". Abort.
Check @prosa.implementation.refinements.refinements.refine_all.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_all". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_flatten". Abort.
Check @prosa.implementation.refinements.refinements.refine_flatten.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_flatten". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_cons". Abort.
Check @prosa.implementation.refinements.refinements.refine_cons.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_cons". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_nil". Abort.
Check @prosa.implementation.refinements.refinements.refine_nil.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_nil". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_last". Abort.
Check @prosa.implementation.refinements.refinements.refine_last.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_last". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_size". Abort.
Check @prosa.implementation.refinements.refinements.refine_size.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_size". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.iotaTsuccN". Abort.
Check @prosa.implementation.refinements.refinements.iotaTsuccN.
Goal True. idtac "END|prosa.implementation.refinements.refinements.iotaTsuccN". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_iota". Abort.
Check @prosa.implementation.refinements.refinements.refine_iota.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_iota". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_shift_points_pos". Abort.
Check @prosa.implementation.refinements.refinements.refine_shift_points_pos.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_shift_points_pos". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_shift_points_neg". Abort.
Check @prosa.implementation.refinements.refinements.refine_shift_points_neg.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_shift_points_neg". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_abstract". Abort.
Check @prosa.implementation.refinements.refinements.refine_abstract.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_abstract". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_foldr_lemma". Abort.
Check @prosa.implementation.refinements.refinements.refine_foldr_lemma.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_foldr_lemma". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_foldr". Abort.
Check @prosa.implementation.refinements.refinements.refine_foldr.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_foldr". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_uncond_foldr". Abort.
Check @prosa.implementation.refinements.refinements.refine_uncond_foldr.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_uncond_foldr". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.refinements.refine_foldr_max". Abort.
Check @prosa.implementation.refinements.refinements.refine_foldr_max.
Goal True. idtac "END|prosa.implementation.refinements.refinements.refine_foldr_max". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.Task". Abort.
Check @prosa.implementation.refinements.task.Task.
Goal True. idtac "END|prosa.implementation.refinements.task.Task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.Job". Abort.
Check @prosa.implementation.refinements.task.Job.
Goal True. idtac "END|prosa.implementation.refinements.task.Job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.task_T". Abort.
Check @prosa.implementation.refinements.task.task_T.
Goal True. idtac "END|prosa.implementation.refinements.task.task_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.task_eqdef_T". Abort.
Check @prosa.implementation.refinements.task.task_eqdef_T.
Goal True. idtac "END|prosa.implementation.refinements.task.task_eqdef_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.inter_arrival_to_extrapolated_arrival_curve_T". Abort.
Check @prosa.implementation.refinements.task.inter_arrival_to_extrapolated_arrival_curve_T.
Goal True. idtac "END|prosa.implementation.refinements.task.inter_arrival_to_extrapolated_arrival_curve_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.get_extrapolated_arrival_curve_T". Abort.
Check @prosa.implementation.refinements.task.get_extrapolated_arrival_curve_T.
Goal True. idtac "END|prosa.implementation.refinements.task.get_extrapolated_arrival_curve_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.ConcreteMaxArrivals_T". Abort.
Check @prosa.implementation.refinements.task.ConcreteMaxArrivals_T.
Goal True. idtac "END|prosa.implementation.refinements.task.ConcreteMaxArrivals_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.task_rbf_T". Abort.
Check @prosa.implementation.refinements.task.task_rbf_T.
Goal True. idtac "END|prosa.implementation.refinements.task.task_rbf_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.valid_arrivals_T". Abort.
Check @prosa.implementation.refinements.task.valid_arrivals_T.
Goal True. idtac "END|prosa.implementation.refinements.task.valid_arrivals_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.get_horizon_of_task_T". Abort.
Check @prosa.implementation.refinements.task.get_horizon_of_task_T.
Goal True. idtac "END|prosa.implementation.refinements.task.get_horizon_of_task_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.get_time_steps_of_task_T". Abort.
Check @prosa.implementation.refinements.task.get_time_steps_of_task_T.
Goal True. idtac "END|prosa.implementation.refinements.task.get_time_steps_of_task_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.time_steps_with_offset_T". Abort.
Check @prosa.implementation.refinements.task.time_steps_with_offset_T.
Goal True. idtac "END|prosa.implementation.refinements.task.time_steps_with_offset_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.repeat_steps_with_offset_T". Abort.
Check @prosa.implementation.refinements.task.repeat_steps_with_offset_T.
Goal True. idtac "END|prosa.implementation.refinements.task.repeat_steps_with_offset_T". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.taskT_to_task". Abort.
Check @prosa.implementation.refinements.task.taskT_to_task.
Goal True. idtac "END|prosa.implementation.refinements.task.taskT_to_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.Rtask". Abort.
Check @prosa.implementation.refinements.task.Rtask.
Goal True. idtac "END|prosa.implementation.refinements.task.Rtask". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.task_to_taskT". Abort.
Check @prosa.implementation.refinements.task.task_to_taskT.
Goal True. idtac "END|prosa.implementation.refinements.task.task_to_taskT". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.refine_task". Abort.
Check @prosa.implementation.refinements.task.refine_task.
Goal True. idtac "END|prosa.implementation.refinements.task.refine_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.refine_task_id". Abort.
Check @prosa.implementation.refinements.task.refine_task_id.
Goal True. idtac "END|prosa.implementation.refinements.task.refine_task_id". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.refine_task_cost". Abort.
Check @prosa.implementation.refinements.task.refine_task_cost.
Goal True. idtac "END|prosa.implementation.refinements.task.refine_task_cost". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.refine_task_arrival". Abort.
Check @prosa.implementation.refinements.task.refine_task_arrival.
Goal True. idtac "END|prosa.implementation.refinements.task.refine_task_arrival". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.refine_task_deadline". Abort.
Check @prosa.implementation.refinements.task.refine_task_deadline.
Goal True. idtac "END|prosa.implementation.refinements.task.refine_task_deadline". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.refine_task_priority". Abort.
Check @prosa.implementation.refinements.task.refine_task_priority.
Goal True. idtac "END|prosa.implementation.refinements.task.refine_task_priority". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.refine_Periodic". Abort.
Check @prosa.implementation.refinements.task.refine_Periodic.
Goal True. idtac "END|prosa.implementation.refinements.task.refine_Periodic". Abort.
Goal True. idtac "BEGIN|prosa.implementation.refinements.task.refine_Sporadic". Abort.
Check @prosa.implementation.refinements.task.refine_Sporadic.
Goal True. idtac "END|prosa.implementation.refinements.task.refine_Sporadic". Abort.
