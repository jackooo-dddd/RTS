import Prosa.Analysis.Facts.Tdma
set_option pp.fieldNotation false

#check @Prosa.Analysis.Facts.Tdma.TDMA_cycle_ge_each_time_slot
#check @Prosa.Analysis.Facts.Tdma.TDMA_cycle_positive
#check @Prosa.Analysis.Facts.Tdma.Offset_lt_cycle
#check @Prosa.Analysis.Facts.Tdma.Offset_add_slot_leq_cycle
#check @Prosa.Analysis.Facts.Tdma.relation_offset
#check @Prosa.Analysis.Facts.Tdma.task_in_time_slot_uniq

#print axioms Prosa.Analysis.Facts.Tdma.TDMA_cycle_ge_each_time_slot
#print axioms Prosa.Analysis.Facts.Tdma.TDMA_cycle_positive
#print axioms Prosa.Analysis.Facts.Tdma.Offset_lt_cycle
#print axioms Prosa.Analysis.Facts.Tdma.Offset_add_slot_leq_cycle
#print axioms Prosa.Analysis.Facts.Tdma.relation_offset
#print axioms Prosa.Analysis.Facts.Tdma.task_in_time_slot_uniq
