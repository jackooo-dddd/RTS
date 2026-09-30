Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsSuspensionSemanticSource.
Import FactsSuspensionSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspended_implies_job_not_ready". Abort.
Print statement_suspended_implies_job_not_ready.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspended_implies_job_not_ready". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspended_implies_not_scheduled". Abort.
Print statement_suspended_implies_not_scheduled.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspended_implies_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspended_implies_arrived". Abort.
Print statement_suspended_implies_arrived.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspended_implies_arrived". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspended_implies_pending". Abort.
Print statement_suspended_implies_pending.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspended_implies_pending". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspended_implies_not_backlogged". Abort.
Print statement_suspended_implies_not_backlogged.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspended_implies_not_backlogged". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.pending_and_not_suspended_implies_ready". Abort.
Print statement_pending_and_not_suspended_implies_ready.
Goal True. idtac "END|prosa.analysis.facts.suspension.pending_and_not_suspended_implies_ready". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspension_bounded_trivial". Abort.
Print statement_suspension_bounded_trivial.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspension_bounded_trivial". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspension_bounded_longer_interval". Abort.
Print statement_suspension_bounded_longer_interval.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspension_bounded_longer_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspension_bounded_in_interval_aux". Abort.
Print statement_suspension_bounded_in_interval_aux.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspension_bounded_in_interval_aux". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.exists_some_point". Abort.
Print statement_exists_some_point.
Goal True. idtac "END|prosa.analysis.facts.suspension.exists_some_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspension_bounded_in_interval". Abort.
Print statement_suspension_bounded_in_interval.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspension_bounded_in_interval". Abort.
