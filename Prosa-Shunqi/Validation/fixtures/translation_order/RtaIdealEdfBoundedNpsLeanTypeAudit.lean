import Prosa.Results.Rta.Ideal.Edf.BoundedNps
set_option pp.fieldNotation false

#check @Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space
#check @Prosa.Results.Rta.Ideal.Edf.BoundedNps.blocking_bound_decreasing
#check @Prosa.Results.Rta.Ideal.Edf.BoundedNps.task_with_equal_deadline_exists
#check @Prosa.Results.Rta.Ideal.Edf.BoundedNps.search_space_inclusion
#check @Prosa.Results.Rta.Ideal.Edf.BoundedNps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments

#print axioms Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space
#print axioms Prosa.Results.Rta.Ideal.Edf.BoundedNps.blocking_bound_decreasing
#print axioms Prosa.Results.Rta.Ideal.Edf.BoundedNps.task_with_equal_deadline_exists
#print axioms Prosa.Results.Rta.Ideal.Edf.BoundedNps.search_space_inclusion
#print axioms Prosa.Results.Rta.Ideal.Edf.BoundedNps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
