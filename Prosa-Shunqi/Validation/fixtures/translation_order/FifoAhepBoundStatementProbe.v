Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FifoAhepBoundSemanticSource.
Import FifoAhepBoundSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.task.arrival.curves prosa.model.priority.fifo.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo_ahep_bound.bound_on_hep_workload". Abort.
Print statement_bound_on_hep_workload.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo_ahep_bound.bound_on_hep_workload". Abort.
