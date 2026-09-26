Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsReadinessBasicSemanticSource.
Import FactsReadinessBasicSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.ReadinessSemanticSource.
Import ReadinessSemanticSource.
Require Import prosa.model.readiness.basic prosa.analysis.definitions.work_bearing_readiness.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.basic.basic_readiness_nonclairvoyance". Abort.
Print statement_basic_readiness_nonclairvoyance.
Goal True. idtac "END|prosa.analysis.facts.readiness.basic.basic_readiness_nonclairvoyance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.basic.basic_readiness_compliance". Abort.
Print statement_basic_readiness_compliance.
Goal True. idtac "END|prosa.analysis.facts.readiness.basic.basic_readiness_compliance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.basic.basic_readiness_is_work_bearing_readiness". Abort.
Print statement_basic_readiness_is_work_bearing_readiness.
Goal True. idtac "END|prosa.analysis.facts.readiness.basic.basic_readiness_is_work_bearing_readiness". Abort.
