import Prosa.Model.Task.Arrival.Sporadic

open Prosa.Model.Task.Arrival.Sporadic

#check @SporadicModel
#check @task_min_inter_arrival_time
#check @valid_task_min_inter_arrival_time
#check @valid_taskset_inter_arrival_times
#check @respects_sporadic_task_model
#check @taskset_respects_sporadic_task_model

#print axioms Prosa.Model.Task.Arrival.Sporadic.valid_task_min_inter_arrival_time
#print axioms Prosa.Model.Task.Arrival.Sporadic.valid_taskset_inter_arrival_times
#print axioms Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model
#print axioms Prosa.Model.Task.Arrival.Sporadic.taskset_respects_sporadic_task_model
