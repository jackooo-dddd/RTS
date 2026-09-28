Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RsAbstractSeqRtaSemanticSource.
Import RsAbstractSeqRtaSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.analysis.abstract.search_space prosa.analysis.abstract.definitions prosa.analysis.abstract.restricted_supply.busy_sbf.
(* display-only: the official elaborated-type evidence was printed with other [is_in_search_space], [work_conserving] and [valid_busy_sbf] in scope, so the abstract ones are displayed qualified *)
Module RsAbstractSeqRtaProbeDisplay. Definition is_in_search_space := tt. Definition work_conserving := tt. Definition valid_busy_sbf := tt. End RsAbstractSeqRtaProbeDisplay.
Import RsAbstractSeqRtaProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.IBF_P_bounds_interference". Abort.
Print statement_IBF_P_bounds_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.IBF_P_bounds_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.sol_seq_rs_equation_impl_sol_rs_equation". Abort.
Print statement_sol_seq_rs_equation_impl_sol_rs_equation.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.sol_seq_rs_equation_impl_sol_rs_equation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.uniprocessor_response_time_bound_restricted_supply_seq". Abort.
Print statement_uniprocessor_response_time_bound_restricted_supply_seq.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.uniprocessor_response_time_bound_restricted_supply_seq". Abort.
