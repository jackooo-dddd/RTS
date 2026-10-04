import Validation.fixtures.translation_order.ClassicExtractionTdmaInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.get_slot
#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.get_cost
#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.get_D
#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.get_P
#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.task_eq
#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.In
#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.schedulable_tsk
#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.schedulability_test
#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.schedulability_test_valid
#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.cycle
#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.schedulability_tdma
#check @Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.schedulability_tdma_valid
#check @Prosa.Validation.ClassicExtractionTdmaInterface.production_sumSeq_nil
#check @Prosa.Validation.ClassicExtractionTdmaInterface.production_sumSeq_cons
#check @Prosa.Validation.ClassicExtractionTdmaInterface.production_sumFiltered_nil
#check @Prosa.Validation.ClassicExtractionTdmaInterface.production_sumFiltered_cons_true
#check @Prosa.Validation.ClassicExtractionTdmaInterface.production_sumFiltered_cons_false
#check @Prosa.Validation.ClassicExtractionTdmaInterface.end_time_option_c0
#check @Prosa.Validation.ClassicExtractionTdmaInterface.end_time_option_wf0
#check @Prosa.Validation.ClassicExtractionTdmaInterface.end_time_option_step
#check @Prosa.Validation.ClassicExtractionTdmaInterface.xt_get_slot_eq
#check @Prosa.Validation.ClassicExtractionTdmaInterface.xt_get_cost_eq
#check @Prosa.Validation.ClassicExtractionTdmaInterface.xt_get_D_eq
#check @Prosa.Validation.ClassicExtractionTdmaInterface.xt_get_P_eq
#check @Prosa.Validation.ClassicExtractionTdmaInterface.xt_In_nil
#check @Prosa.Validation.ClassicExtractionTdmaInterface.xt_In_cons
#check @Prosa.Validation.ClassicExtractionTdmaInterface.xt_test_nil
#check @Prosa.Validation.ClassicExtractionTdmaInterface.xt_test_cons
#check @Prosa.Validation.ClassicExtractionTdmaInterface.xt_cycle_nil
#check @Prosa.Validation.ClassicExtractionTdmaInterface.xt_cycle_cons
#check @Prosa.Validation.ClassicExtractionTdmaInterface.xt_schedulable_tsk_eq
#check @Prosa.Validation.DivModInterface.production_div_floor_eq
#check @Prosa.Validation.DivModInterface.production_div_ceil_eq
#check @Prosa.Validation.DivModInterface.production_div_add_mod
#check @Prosa.Validation.DivModInterface.production_mod_lt
#check @Prosa.Validation.DivModInterface.production_div_zero
#check @Prosa.Validation.DivModInterface.production_mod_zero
#check @Prosa.Validation.DivModInterface.production_dvd_iff_mod_eq_zero

#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.get_slot
#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.get_cost
#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.get_D
#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.get_P
#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.task_eq
#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.In
#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.schedulable_tsk
#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.schedulability_test
#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.schedulability_test_valid
#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.cycle
#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.schedulability_tdma
#print axioms Prosa.Classic.Implementation.Uni.Basic.ExtractionTdma.schedulability_tdma_valid
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.production_sumSeq_nil
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.production_sumSeq_cons
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.production_sumFiltered_nil
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.production_sumFiltered_cons_true
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.production_sumFiltered_cons_false
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.end_time_option_c0
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.end_time_option_wf0
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.end_time_option_step
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.xt_get_slot_eq
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.xt_get_cost_eq
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.xt_get_D_eq
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.xt_get_P_eq
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.xt_In_nil
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.xt_In_cons
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.xt_test_nil
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.xt_test_cons
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.xt_cycle_nil
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.xt_cycle_cons
#print axioms Prosa.Validation.ClassicExtractionTdmaInterface.xt_schedulable_tsk_eq
#print axioms Prosa.Validation.DivModInterface.production_div_floor_eq
#print axioms Prosa.Validation.DivModInterface.production_div_ceil_eq
#print axioms Prosa.Validation.DivModInterface.production_div_add_mod
#print axioms Prosa.Validation.DivModInterface.production_mod_lt
#print axioms Prosa.Validation.DivModInterface.production_div_zero
#print axioms Prosa.Validation.DivModInterface.production_mod_zero
#print axioms Prosa.Validation.DivModInterface.production_dvd_iff_mod_eq_zero
