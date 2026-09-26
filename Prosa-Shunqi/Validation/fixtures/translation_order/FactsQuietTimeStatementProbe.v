Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsQuietTimeSemanticSource.
Import FactsQuietTimeSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all.
Require Import prosa.analysis.definitions.carry_in.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.quiet_time.zero_is_quiet_time". Abort.
Print statement_zero_is_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.quiet_time.zero_is_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.quiet_time.no_carry_in_implies_quiet_time". Abort.
Print statement_no_carry_in_implies_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.quiet_time.no_carry_in_implies_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.quiet_time.busy_interval_prefix_no_quiet_time". Abort.
Print statement_busy_interval_prefix_no_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.quiet_time.busy_interval_prefix_no_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.quiet_time.busy_interval_no_quiet_time". Abort.
Print statement_busy_interval_no_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.quiet_time.busy_interval_no_quiet_time". Abort.
