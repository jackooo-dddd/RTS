Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BlackoutBoundSemanticSource.
Import BlackoutBoundSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: in the official environment [ideal.processor_state] is also in scope, so the overheads
   processor model prints module-qualified; this shadow reproduces that display (no statement is affected). *)
Module ideal_display. Definition processor_state := tt. End ideal_display. Import ideal_display.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.blackout_during_split". Abort.
Print statement_blackout_during_split.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.blackout_during_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_dispatch_time_eq_job_dispatch_time". Abort.
Print statement_total_dispatch_time_eq_job_dispatch_time.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_dispatch_time_eq_job_dispatch_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_cswitch_time_eq_job_cswitch_time". Abort.
Print statement_total_cswitch_time_eq_job_cswitch_time.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_cswitch_time_eq_job_cswitch_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_CRPD_time_eq_job_CRPD_time". Abort.
Print statement_total_CRPD_time_eq_job_CRPD_time.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_CRPD_time_eq_job_CRPD_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_dispatch_is_bounded". Abort.
Print statement_total_time_in_dispatch_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_dispatch_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_cswitch_is_bounded". Abort.
Print statement_total_time_in_cswitch_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_cswitch_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_CRPD_is_bounded". Abort.
Print statement_total_time_in_CRPD_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_CRPD_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.no_sched_changes_bounded_overheads_blackout". Abort.
Print statement_no_sched_changes_bounded_overheads_blackout.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.no_sched_changes_bounded_overheads_blackout". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.sched_changes_start_busy_pref_bounded_overheads_blackout". Abort.
Print statement_sched_changes_start_busy_pref_bounded_overheads_blackout.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.sched_changes_start_busy_pref_bounded_overheads_blackout". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.fin_sched_changes_start_busy_pref_bounded_overheads_blackout". Abort.
Print statement_fin_sched_changes_start_busy_pref_bounded_overheads_blackout.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.fin_sched_changes_start_busy_pref_bounded_overheads_blackout". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.finite_sched_changes_bounded_overheads_blackout". Abort.
Print statement_finite_sched_changes_bounded_overheads_blackout.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.finite_sched_changes_bounded_overheads_blackout". Abort.
