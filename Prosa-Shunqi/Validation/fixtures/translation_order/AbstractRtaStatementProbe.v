Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.AbstractRtaSemanticSource.
Import AbstractRtaSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.analysis.abstract.definitions.
(* display-only: the official elaborated-type evidence was printed with the classical
   busy-interval notions and a second search-space predicate in scope, so the abstract
   ones are displayed qualified as [definitions.busy_interval] and
   [search_space.is_in_search_space] *)
Module AbstractRtaProbeDisplay.
  Definition busy_interval_prefix := tt. Definition busy_interval := tt.
  Definition quiet_time := tt. Definition work_conserving := tt.
  Definition is_in_search_space := tt.
End AbstractRtaProbeDisplay.
Import AbstractRtaProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.relative_arrival_time_of_job_is_A". Abort.
Check @relative_arrival_time_of_job_is_A.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.relative_arrival_time_of_job_is_A". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.relative_time_to_reach_rtct". Abort.
Check @relative_time_to_reach_rtct.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.relative_time_to_reach_rtct". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_arrival_eq_t1_plus_A". Abort.
Print statement_job_arrival_eq_t1_plus_A.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_arrival_eq_t1_plus_A". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.relative_arrival_is_bounded". Abort.
Print statement_relative_arrival_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.relative_arrival_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_1". Abort.
Print statement_t2_le_arrival_plus_R_1.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_1". Abort.
Print statement_job_completed_by_arrival_plus_R_1.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_2". Abort.
Print statement_t2_le_arrival_plus_R_2.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_2". Abort.
Print statement_job_completed_by_arrival_plus_R_2.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.relative_rtc_time_is_bounded". Abort.
Print statement_relative_rtc_time_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.relative_rtc_time_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_1". Abort.
Print statement_job_receives_enough_service_1.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_2". Abort.
Print statement_job_receives_enough_service_2.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_3". Abort.
Print statement_job_receives_enough_service_3.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_3". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_is_completed_by_arrival_plus_R". Abort.
Print statement_job_is_completed_by_arrival_plus_R.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_is_completed_by_arrival_plus_R". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.uniprocessor_response_time_bound". Abort.
Print statement_uniprocessor_response_time_bound.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.uniprocessor_response_time_bound". Abort.
