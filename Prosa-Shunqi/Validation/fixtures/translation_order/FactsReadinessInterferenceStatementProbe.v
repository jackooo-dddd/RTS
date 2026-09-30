Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsReadinessInterferenceSemanticSource.
Import FactsReadinessInterferenceSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_another_hep_interference". Abort.
Print statement_no_hep_ready_implies_no_another_hep_interference.
Goal True. idtac "END|prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_another_hep_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_service_inversion". Abort.
Print statement_no_hep_ready_implies_no_service_inversion.
Goal True. idtac "END|prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_service_inversion". Abort.
