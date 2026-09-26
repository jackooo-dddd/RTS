Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsReplaceAtSemanticSource.
Import FactsReplaceAtSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.analysis.transform.swap.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.replace_at_def". Abort.
Print statement_replace_at_def.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.replace_at_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.rest_of_schedule_invariant". Abort.
Print statement_rest_of_schedule_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.rest_of_schedule_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.service_at_other_times_invariant". Abort.
Print statement_service_at_other_times_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.service_at_other_times_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.service_delta". Abort.
Print statement_service_delta.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.service_delta". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.service_in_replaced". Abort.
Print statement_service_in_replaced.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.service_in_replaced". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.service_at_of_others_invariant". Abort.
Print statement_service_at_of_others_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.service_at_of_others_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.service_during_of_others_invariant". Abort.
Print statement_service_during_of_others_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.service_during_of_others_invariant". Abort.
