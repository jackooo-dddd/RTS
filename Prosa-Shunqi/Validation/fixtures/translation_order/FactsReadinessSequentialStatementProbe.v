Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsReadinessSequentialSemanticSource.
Import FactsReadinessSequentialSemanticSource.
(* display-only: the same imports as the extracted module, so names print as in the evidence *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.analysis.definitions.readiness.
Require Import prosa.model.readiness.sequential prosa.analysis.definitions.work_bearing_readiness.
Module ReadinessDisplay. Definition sequential_readiness := tt. End ReadinessDisplay. Import ReadinessDisplay.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.sequential.sequential_readiness_is_sequential". Abort.
Print statement_sequential_readiness_is_sequential.
Goal True. idtac "END|prosa.analysis.facts.readiness.sequential.sequential_readiness_is_sequential". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.sequential.sequential_readiness_nonclairvoyance". Abort.
Print statement_sequential_readiness_nonclairvoyance.
Goal True. idtac "END|prosa.analysis.facts.readiness.sequential.sequential_readiness_nonclairvoyance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_sequential_tasks". Abort.
Print statement_sequential_readiness_implies_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_work_bearing_readiness". Abort.
Print statement_sequential_readiness_implies_work_bearing_readiness.
Goal True. idtac "END|prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_work_bearing_readiness". Abort.
