Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.IdealAbstractRtaSemanticSource.
Import IdealAbstractRtaSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.analysis.abstract.definitions.
(* display-only: the official elaborated-type evidence was printed with the classical
   busy-interval notions and a second search-space predicate in scope, so the abstract
   ones are displayed qualified as [definitions.work_conserving] and
   [search_space.is_in_search_space] *)
Module IdealAbstractRtaProbeDisplay.
  Definition busy_interval_prefix := tt. Definition busy_interval := tt.
  Definition quiet_time := tt. Definition work_conserving := tt.
  Definition is_in_search_space := tt.
End IdealAbstractRtaProbeDisplay.
Import IdealAbstractRtaProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.abstract_rta.nonpreemptive_interference_is_bounded". Abort.
Print statement_nonpreemptive_interference_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.ideal.abstract_rta.nonpreemptive_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.abstract_rta.uniprocessor_response_time_bound_ideal". Abort.
Print statement_uniprocessor_response_time_bound_ideal.
Goal True. idtac "END|prosa.analysis.abstract.ideal.abstract_rta.uniprocessor_response_time_bound_ideal". Abort.
