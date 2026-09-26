Require Export prosa.util.all.
Require Export prosa.model.task.arrival.request_bound_functions.
Require Export prosa.model.task.arrival.curves.

Module CurveAsRbfSemanticSource.

Section SourceContext_0.
  Context {Task : TaskType} `{TaskCost Task} `{TaskMinCost Task}.
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job}.
  Context `{MaxArr : MaxArrivals Task} `{MinArr : MinArrivals Task}.

  Definition task_max_rbf (arrivals :  Task -> duration -> nat) task Δ := task_cost task * arrivals task Δ.

End SourceContext_0.

Section SourceContext_1.
  Context {Task : TaskType} `{TaskCost Task} `{TaskMinCost Task}.
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job}.
  Context `{MaxArr : MaxArrivals Task} `{MinArr : MinArrivals Task}.

  Definition task_min_rbf (arrivals :  Task -> duration -> nat) task Δ := task_min_cost task * arrivals task Δ.

End SourceContext_1.

Section SourceContext_2.
  Context {Task : TaskType} `{TaskCost Task} `{TaskMinCost Task}.
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job}.
  Context `{MaxArr : MaxArrivals Task} `{MinArr : MinArrivals Task}.

  Global Program Instance MaxArrivalsRBF : MaxRequestBound Task := task_max_rbf max_arrivals.

End SourceContext_2.

Section SourceContext_3.
  Context {Task : TaskType} `{TaskCost Task} `{TaskMinCost Task}.
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job}.
  Context `{MaxArr : MaxArrivals Task} `{MinArr : MinArrivals Task}.

  Global Program Instance MinArrivalsRBF : MinRequestBound Task := task_min_rbf min_arrivals.

End SourceContext_3.

Definition statement_valid_arrival_curve_to_max_rbf : Prop :=
  (forall (Task : TaskType) (H : TaskCost Task) (tsk : Task) (arrivals : Task -> duration -> nat), valid_arrival_curve (arrivals tsk) -> valid_request_bound_function (task_max_rbf arrivals tsk)).

Definition statement_valid_arrival_curve_to_min_rbf : Prop :=
  (forall (Task : TaskType) (H0 : TaskMinCost Task) (tsk : Task) (arrivals : Task -> duration -> nat), valid_arrival_curve (arrivals tsk) -> valid_request_bound_function (task_min_rbf arrivals tsk)).

Definition statement_respects_arrival_curve_to_max_rbf : Prop :=
  (forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H1 : JobTask Job Task) (H2 : JobCost Job) (MaxArr : MaxArrivals Task) (tsk : Task) (arr_seq : arrival_sequence Job), jobs_have_valid_job_costs -> respects_max_arrivals arr_seq tsk (MaxArr tsk) -> respects_max_request_bound arr_seq tsk (task_max_rbf MaxArr tsk)).

Definition statement_respects_arrival_curve_to_min_rbf : Prop :=
  (forall (Task : TaskType) (H0 : TaskMinCost Task) (Job : JobType) (H1 : JobTask Job Task) (H2 : JobCost Job) (MinArr : MinArrivals Task) (tsk : Task) (arr_seq : arrival_sequence Job), jobs_have_valid_min_job_costs -> respects_min_arrivals arr_seq tsk (MinArr tsk) -> respects_min_request_bound arr_seq tsk (task_min_rbf MinArr tsk)).

Definition statement_valid_taskset_arrival_curve_to_max_rbf : Prop :=
  (forall (Task : TaskType) (H : TaskCost Task) (MaxArr : MaxArrivals Task) (ts : TaskSet Task), valid_taskset_arrival_curve ts MaxArr -> valid_taskset_request_bound_function ts MaxArrivalsRBF).

Definition statement_valid_taskset_arrival_curve_to_min_rbf : Prop :=
  (forall (Task : TaskType) (H0 : TaskMinCost Task) (MinArr : MinArrivals Task) (ts : TaskSet Task), valid_taskset_arrival_curve ts MinArr -> valid_taskset_request_bound_function ts MinArrivalsRBF).

Definition statement_taskset_respects_arrival_curve_to_max_rbf : Prop :=
  (forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H1 : JobTask Job Task) (H2 : JobCost Job) (MaxArr : MaxArrivals Task) (ts : TaskSet Task) (arr_seq : arrival_sequence Job), jobs_have_valid_job_costs -> taskset_respects_max_arrivals arr_seq ts -> taskset_respects_max_request_bound arr_seq ts).

Definition statement_taskset_respects_arrival_curve_to_min_rbf : Prop :=
  (forall (Task : TaskType) (H0 : TaskMinCost Task) (Job : JobType) (H1 : JobTask Job Task) (H2 : JobCost Job) (MinArr : MinArrivals Task) (ts : TaskSet Task) (arr_seq : arrival_sequence Job), jobs_have_valid_min_job_costs -> taskset_respects_min_arrivals arr_seq ts -> taskset_respects_min_request_bound arr_seq ts).

End CurveAsRbfSemanticSource.
