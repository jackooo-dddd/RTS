import Prosa.Results.Rta.Ideal.Fifo.BoundedNps
set_option pp.fieldNotation false

#check @Prosa.Results.Rta.Ideal.Fifo.BoundedNps.abstractly_work_conserving
#check @Prosa.Results.Rta.Ideal.Fifo.BoundedNps.busy_windows_are_bounded
#check @Prosa.Results.Rta.Ideal.Fifo.BoundedNps.no_priority_inversion
#check @Prosa.Results.Rta.Ideal.Fifo.BoundedNps.IBF_correct
#check @Prosa.Results.Rta.Ideal.Fifo.BoundedNps.is_in_concrete_search_space
#check @Prosa.Results.Rta.Ideal.Fifo.BoundedNps.search_space_refinement
#check @Prosa.Results.Rta.Ideal.Fifo.BoundedNps.soln_abstract_response_time_recurrence
#check @Prosa.Results.Rta.Ideal.Fifo.BoundedNps.uniprocessor_response_time_bound_FIFO

#print axioms Prosa.Results.Rta.Ideal.Fifo.BoundedNps.abstractly_work_conserving
#print axioms Prosa.Results.Rta.Ideal.Fifo.BoundedNps.busy_windows_are_bounded
#print axioms Prosa.Results.Rta.Ideal.Fifo.BoundedNps.no_priority_inversion
#print axioms Prosa.Results.Rta.Ideal.Fifo.BoundedNps.IBF_correct
#print axioms Prosa.Results.Rta.Ideal.Fifo.BoundedNps.is_in_concrete_search_space
#print axioms Prosa.Results.Rta.Ideal.Fifo.BoundedNps.search_space_refinement
#print axioms Prosa.Results.Rta.Ideal.Fifo.BoundedNps.soln_abstract_response_time_recurrence
#print axioms Prosa.Results.Rta.Ideal.Fifo.BoundedNps.uniprocessor_response_time_bound_FIFO
