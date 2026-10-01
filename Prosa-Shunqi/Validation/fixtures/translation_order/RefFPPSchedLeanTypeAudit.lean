import Prosa.Implementation.Refinements.FP.PreemptiveSched
set_option pp.fieldNotation false

#check @Prosa.Implementation.Refinements.FP.PreemptiveSched.Task
#check @Prosa.Implementation.Refinements.FP.PreemptiveSched.Job
#check @Prosa.Implementation.Refinements.FP.PreemptiveSched.sequential_ready_instance
#check @Prosa.Implementation.Refinements.FP.PreemptiveSched.sched
#check @Prosa.Implementation.Refinements.FP.PreemptiveSched.sched_valid
#check @Prosa.Implementation.Refinements.FP.PreemptiveSched.respects_policy_at_preemption_point

#print axioms Prosa.Implementation.Refinements.FP.PreemptiveSched.Task
#print axioms Prosa.Implementation.Refinements.FP.PreemptiveSched.Job
#print axioms Prosa.Implementation.Refinements.FP.PreemptiveSched.sequential_ready_instance
#print axioms Prosa.Implementation.Refinements.FP.PreemptiveSched.sched
#print axioms Prosa.Implementation.Refinements.FP.PreemptiveSched.sched_valid
#print axioms Prosa.Implementation.Refinements.FP.PreemptiveSched.respects_policy_at_preemption_point
