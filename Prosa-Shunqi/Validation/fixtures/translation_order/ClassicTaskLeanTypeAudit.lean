import Prosa.Classic.Model.Arrival.Basic.Task
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_positive
#check @Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_period_positive
#check @Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_deadline_positive
#check @Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_le_deadline
#check @Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_le_period
#check @Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.is_valid_sporadic_task
#check @Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset.taskset_of
#check @Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset.valid_sporadic_taskset
#check @Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset.implicit_deadline_model
#check @Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset.constrained_deadline_model
#check @Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset.arbitrary_deadline_model

#print axioms Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_positive
#print axioms Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_period_positive
#print axioms Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_deadline_positive
#print axioms Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_le_deadline
#print axioms Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_le_period
#print axioms Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.is_valid_sporadic_task
#print axioms Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset.taskset_of
#print axioms Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset.valid_sporadic_taskset
#print axioms Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset.implicit_deadline_model
#print axioms Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset.constrained_deadline_model
#print axioms Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset.arbitrary_deadline_model
