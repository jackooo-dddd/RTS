import Validation.fixtures.translation_order.ClassicUniFpRtaCompInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.max_steps
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.per_task_rta
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_schedulable
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_for_every_task
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_from_taskset
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_computes_iteration
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_yields_fixed_point
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_le_deadline
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_gt_zero
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_analysis_yields_response_time_bounds
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.taskset_schedulable_by_fp_rta
#check @Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.jobs_schedulable_by_fp_rta
#check @Prosa.Validation.ClassicUniFpRtaCompInterface.bigCat_range'
#check @Prosa.Validation.ClassicUniFpRtaCompInterface.production_sumSeq_nil
#check @Prosa.Validation.ClassicUniFpRtaCompInterface.production_sumSeq_cons
#check @Prosa.Validation.ClassicUniFpRtaCompInterface.production_sumFiltered_nil
#check @Prosa.Validation.ClassicUniFpRtaCompInterface.production_sumFiltered_cons_true
#check @Prosa.Validation.ClassicUniFpRtaCompInterface.production_sumFiltered_cons_false
#check @Prosa.Validation.DivModInterface.production_div_floor_eq
#check @Prosa.Validation.DivModInterface.production_div_ceil_eq
#check @Prosa.Validation.DivModInterface.production_div_add_mod
#check @Prosa.Validation.DivModInterface.production_mod_lt
#check @Prosa.Validation.DivModInterface.production_div_zero
#check @Prosa.Validation.DivModInterface.production_mod_zero
#check @Prosa.Validation.DivModInterface.production_dvd_iff_mod_eq_zero

#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.max_steps
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.per_task_rta
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_schedulable
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_for_every_task
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_from_taskset
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_computes_iteration
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_yields_fixed_point
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_le_deadline
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_claimed_bounds_gt_zero
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.fp_analysis_yields_response_time_bounds
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.taskset_schedulable_by_fp_rta
#print axioms Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP.jobs_schedulable_by_fp_rta
#print axioms Prosa.Validation.ClassicUniFpRtaCompInterface.bigCat_range'
#print axioms Prosa.Validation.ClassicUniFpRtaCompInterface.production_sumSeq_nil
#print axioms Prosa.Validation.ClassicUniFpRtaCompInterface.production_sumSeq_cons
#print axioms Prosa.Validation.ClassicUniFpRtaCompInterface.production_sumFiltered_nil
#print axioms Prosa.Validation.ClassicUniFpRtaCompInterface.production_sumFiltered_cons_true
#print axioms Prosa.Validation.ClassicUniFpRtaCompInterface.production_sumFiltered_cons_false
#print axioms Prosa.Validation.DivModInterface.production_div_floor_eq
#print axioms Prosa.Validation.DivModInterface.production_div_ceil_eq
#print axioms Prosa.Validation.DivModInterface.production_div_add_mod
#print axioms Prosa.Validation.DivModInterface.production_mod_lt
#print axioms Prosa.Validation.DivModInterface.production_div_zero
#print axioms Prosa.Validation.DivModInterface.production_mod_zero
#print axioms Prosa.Validation.DivModInterface.production_dvd_iff_mod_eq_zero
