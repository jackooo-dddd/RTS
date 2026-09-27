Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RsAbstractRtaSemanticSource.
Import RsAbstractRtaSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.analysis.abstract.definitions.
(* display-only: the official elaborated-type evidence was printed with the classical
   busy-interval notions, a second search-space predicate and the classical busy SBF in
   scope, so the abstract ones are displayed qualified as [definitions.work_conserving],
   [search_space.is_in_search_space] and [busy_sbf.valid_busy_sbf] *)
Module RsAbstractRtaProbeDisplay.
  Definition busy_interval_prefix := tt. Definition busy_interval := tt.
  Definition quiet_time := tt. Definition work_conserving := tt.
  Definition is_in_search_space := tt. Definition valid_busy_sbf := tt.
End RsAbstractRtaProbeDisplay.
Import RsAbstractRtaProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_impl_interference". Abort.
Print statement_blackout_impl_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_impl_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_plus_local_is_interference". Abort.
Print statement_blackout_plus_local_is_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_plus_local_is_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_plus_local_is_interference_cumul". Abort.
Print statement_blackout_plus_local_is_interference_cumul.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_plus_local_is_interference_cumul". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.cumulative_job_interference_bound". Abort.
Print statement_cumulative_job_interference_bound.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.cumulative_job_interference_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.no_intra_interference_after_F". Abort.
Print statement_no_intra_interference_after_F.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.no_intra_interference_after_F". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_bounds_interference". Abort.
Print statement_IBF_P_bounds_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_bounds_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_NP_bounds_interference". Abort.
Print statement_IBF_NP_bounds_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_NP_bounds_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_sol_le_IBF_NP". Abort.
Print statement_IBF_P_sol_le_IBF_NP.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_sol_le_IBF_NP". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.max_in_rs_hypothesis_impl_max_in_arta_hypothesis". Abort.
Print statement_max_in_rs_hypothesis_impl_max_in_arta_hypothesis.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.max_in_rs_hypothesis_impl_max_in_arta_hypothesis". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.uniprocessor_response_time_bound_restricted_supply". Abort.
Print statement_uniprocessor_response_time_bound_restricted_supply.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.uniprocessor_response_time_bound_restricted_supply". Abort.
