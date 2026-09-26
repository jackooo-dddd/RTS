Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsDeadlinesSemanticSource.
Import FactsDeadlinesSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.deadlines.incomplete_implies_later_deadline". Abort.
Print statement_incomplete_implies_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.behavior.deadlines.incomplete_implies_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.deadlines.incomplete_implies_scheduled_later". Abort.
Print statement_incomplete_implies_scheduled_later.
Goal True. idtac "END|prosa.analysis.facts.behavior.deadlines.incomplete_implies_scheduled_later". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.deadlines.scheduled_at_implies_later_deadline". Abort.
Print statement_scheduled_at_implies_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.behavior.deadlines.scheduled_at_implies_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.deadlines.service_invariant_implies_deadline_met". Abort.
Print statement_service_invariant_implies_deadline_met.
Goal True. idtac "END|prosa.analysis.facts.behavior.deadlines.service_invariant_implies_deadline_met". Abort.
