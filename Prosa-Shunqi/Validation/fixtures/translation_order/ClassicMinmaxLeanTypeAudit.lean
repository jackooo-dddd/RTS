import Validation.fixtures.translation_order.ClassicMinmaxInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Util.Minmax.seq_argmin
#check @Prosa.Classic.Util.Minmax.seq_argmax
#check @Prosa.Classic.Util.Minmax.seq_argmin_exists
#check @Prosa.Classic.Util.Minmax.seq_argmin_in_seq
#check @Prosa.Classic.Util.Minmax.seq_argmax_exists
#check @Prosa.Classic.Util.Minmax.seq_argmax_in_seq
#check @Prosa.Classic.Util.Minmax.seq_argmin_computes_min
#check @Prosa.Classic.Util.Minmax.seq_argmax_computes_max
#check @Prosa.Classic.Util.Minmax.seq_min
#check @Prosa.Classic.Util.Minmax.seq_max
#check @Prosa.Classic.Util.Minmax.seq_min_exists
#check @Prosa.Classic.Util.Minmax.seq_min_in_seq
#check @Prosa.Classic.Util.Minmax.seq_max_exists
#check @Prosa.Classic.Util.Minmax.seq_max_in_seq
#check @Prosa.Classic.Util.Minmax.seq_min_computes_min
#check @Prosa.Classic.Util.Minmax.seq_max_computes_max
#check @Prosa.Classic.Util.Minmax.seq_argmin_nat
#check @Prosa.Classic.Util.Minmax.seq_argmax_nat
#check @Prosa.Classic.Util.Minmax.seq_argmin_nat_exists
#check @Prosa.Classic.Util.Minmax.seq_argmin_nat_in_seq
#check @Prosa.Classic.Util.Minmax.seq_argmax_nat_exists
#check @Prosa.Classic.Util.Minmax.seq_argmax_nat_in_seq
#check @Prosa.Classic.Util.Minmax.seq_argmin_nat_computes_min
#check @Prosa.Classic.Util.Minmax.seq_argmax_nat_computes_max
#check @Prosa.Classic.Util.Minmax.seq_min_nat
#check @Prosa.Classic.Util.Minmax.seq_max_nat
#check @Prosa.Classic.Util.Minmax.seq_min_nat_exists
#check @Prosa.Classic.Util.Minmax.seq_min_nat_in_seq
#check @Prosa.Classic.Util.Minmax.seq_max_nat_exists
#check @Prosa.Classic.Util.Minmax.seq_max_nat_in_seq
#check @Prosa.Classic.Util.Minmax.seq_min_nat_computes_min
#check @Prosa.Classic.Util.Minmax.seq_max_nat_computes_max
#check @Prosa.Classic.Util.Minmax.values_between
#check @Prosa.Classic.Util.Minmax.mem_values_between
#check @Prosa.Classic.Util.Minmax.min_nat_cond
#check @Prosa.Classic.Util.Minmax.max_nat_cond
#check @Prosa.Classic.Util.Minmax.min_nat_cond_exists
#check @Prosa.Classic.Util.Minmax.min_nat_cond_in_seq
#check @Prosa.Classic.Util.Minmax.min_nat_cond_computes_min
#check @Prosa.Classic.Util.Minmax.max_nat_cond_exists
#check @Prosa.Classic.Util.Minmax.max_nat_cond_in_seq
#check @Prosa.Classic.Util.Minmax.max_nat_cond_computes_max
#check @Prosa.Classic.Util.Minmax.seq_argmin_k
#check @Prosa.Classic.Util.Minmax.seq_argmin_k_exists
#check @Prosa.Validation.ClassicMinmaxInterface.finRange_map_shift
#check @Prosa.Validation.ClassicMinmaxInterface.finRange_map_val

#print axioms Prosa.Classic.Util.Minmax.seq_argmin
#print axioms Prosa.Classic.Util.Minmax.seq_argmax
#print axioms Prosa.Classic.Util.Minmax.seq_argmin_exists
#print axioms Prosa.Classic.Util.Minmax.seq_argmin_in_seq
#print axioms Prosa.Classic.Util.Minmax.seq_argmax_exists
#print axioms Prosa.Classic.Util.Minmax.seq_argmax_in_seq
#print axioms Prosa.Classic.Util.Minmax.seq_argmin_computes_min
#print axioms Prosa.Classic.Util.Minmax.seq_argmax_computes_max
#print axioms Prosa.Classic.Util.Minmax.seq_min
#print axioms Prosa.Classic.Util.Minmax.seq_max
#print axioms Prosa.Classic.Util.Minmax.seq_min_exists
#print axioms Prosa.Classic.Util.Minmax.seq_min_in_seq
#print axioms Prosa.Classic.Util.Minmax.seq_max_exists
#print axioms Prosa.Classic.Util.Minmax.seq_max_in_seq
#print axioms Prosa.Classic.Util.Minmax.seq_min_computes_min
#print axioms Prosa.Classic.Util.Minmax.seq_max_computes_max
#print axioms Prosa.Classic.Util.Minmax.seq_argmin_nat
#print axioms Prosa.Classic.Util.Minmax.seq_argmax_nat
#print axioms Prosa.Classic.Util.Minmax.seq_argmin_nat_exists
#print axioms Prosa.Classic.Util.Minmax.seq_argmin_nat_in_seq
#print axioms Prosa.Classic.Util.Minmax.seq_argmax_nat_exists
#print axioms Prosa.Classic.Util.Minmax.seq_argmax_nat_in_seq
#print axioms Prosa.Classic.Util.Minmax.seq_argmin_nat_computes_min
#print axioms Prosa.Classic.Util.Minmax.seq_argmax_nat_computes_max
#print axioms Prosa.Classic.Util.Minmax.seq_min_nat
#print axioms Prosa.Classic.Util.Minmax.seq_max_nat
#print axioms Prosa.Classic.Util.Minmax.seq_min_nat_exists
#print axioms Prosa.Classic.Util.Minmax.seq_min_nat_in_seq
#print axioms Prosa.Classic.Util.Minmax.seq_max_nat_exists
#print axioms Prosa.Classic.Util.Minmax.seq_max_nat_in_seq
#print axioms Prosa.Classic.Util.Minmax.seq_min_nat_computes_min
#print axioms Prosa.Classic.Util.Minmax.seq_max_nat_computes_max
#print axioms Prosa.Classic.Util.Minmax.values_between
#print axioms Prosa.Classic.Util.Minmax.mem_values_between
#print axioms Prosa.Classic.Util.Minmax.min_nat_cond
#print axioms Prosa.Classic.Util.Minmax.max_nat_cond
#print axioms Prosa.Classic.Util.Minmax.min_nat_cond_exists
#print axioms Prosa.Classic.Util.Minmax.min_nat_cond_in_seq
#print axioms Prosa.Classic.Util.Minmax.min_nat_cond_computes_min
#print axioms Prosa.Classic.Util.Minmax.max_nat_cond_exists
#print axioms Prosa.Classic.Util.Minmax.max_nat_cond_in_seq
#print axioms Prosa.Classic.Util.Minmax.max_nat_cond_computes_max
#print axioms Prosa.Classic.Util.Minmax.seq_argmin_k
#print axioms Prosa.Classic.Util.Minmax.seq_argmin_k_exists
#print axioms Prosa.Validation.ClassicMinmaxInterface.finRange_map_shift
#print axioms Prosa.Validation.ClassicMinmaxInterface.finRange_map_val
