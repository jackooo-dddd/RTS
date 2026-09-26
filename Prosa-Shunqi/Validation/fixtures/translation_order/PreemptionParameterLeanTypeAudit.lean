import Prosa.Model.Preemption.Parameter
set_option pp.fieldNotation false

#check @Prosa.Model.Preemption.Parameter.JobPreemptable
#check @Prosa.Model.Preemption.Parameter.job_preemption_points
#check @Prosa.Model.Preemption.Parameter.conversion_preserves_equivalence
#check @Prosa.Model.Preemption.Parameter.lengths_of_segments
#check @Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment
#check @Prosa.Model.Preemption.Parameter.job_last_nonpreemptive_segment
#check @Prosa.Model.Preemption.Parameter.job_rtct
#check @Prosa.Model.Preemption.Parameter.preempted_at
#check @Prosa.Model.Preemption.Parameter.job_cannot_become_nonpreemptive_before_execution
#check @Prosa.Model.Preemption.Parameter.job_cannot_be_nonpreemptive_after_completion
#check @Prosa.Model.Preemption.Parameter.not_preemptive_implies_scheduled
#check @Prosa.Model.Preemption.Parameter.execution_starts_with_preemption_point
#check @Prosa.Model.Preemption.Parameter.valid_preemption_model
#check @Prosa.Model.Preemption.Parameter.no_superfluous_preemptions

#print axioms Prosa.Model.Preemption.Parameter.job_preemption_points
#print axioms Prosa.Model.Preemption.Parameter.conversion_preserves_equivalence
#print axioms Prosa.Model.Preemption.Parameter.lengths_of_segments
#print axioms Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment
#print axioms Prosa.Model.Preemption.Parameter.job_last_nonpreemptive_segment
#print axioms Prosa.Model.Preemption.Parameter.job_rtct
#print axioms Prosa.Model.Preemption.Parameter.preempted_at
#print axioms Prosa.Model.Preemption.Parameter.job_cannot_become_nonpreemptive_before_execution
#print axioms Prosa.Model.Preemption.Parameter.job_cannot_be_nonpreemptive_after_completion
#print axioms Prosa.Model.Preemption.Parameter.not_preemptive_implies_scheduled
#print axioms Prosa.Model.Preemption.Parameter.execution_starts_with_preemption_point
#print axioms Prosa.Model.Preemption.Parameter.valid_preemption_model
#print axioms Prosa.Model.Preemption.Parameter.no_superfluous_preemptions
#print axioms Prosa.Model.Preemption.Parameter.JobPreemptable
