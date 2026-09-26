Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.ReadinessSemanticSource.
Import ReadinessSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.PreemptionParameterSemanticSource.
Import PreemptionParameterSemanticSource.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness.nonclairvoyant_readiness". Abort.
Check @nonclairvoyant_readiness.
Goal True. idtac "END|prosa.analysis.definitions.readiness.nonclairvoyant_readiness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness.valid_nonpreemptive_readiness". Abort.
Check @valid_nonpreemptive_readiness.
Goal True. idtac "END|prosa.analysis.definitions.readiness.valid_nonpreemptive_readiness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness.sequential_readiness". Abort.
Check @sequential_readiness.
Goal True. idtac "END|prosa.analysis.definitions.readiness.sequential_readiness". Abort.
