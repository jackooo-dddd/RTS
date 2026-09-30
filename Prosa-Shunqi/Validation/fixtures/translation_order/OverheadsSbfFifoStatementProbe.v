Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.OverheadsSbfFifoSemanticSource.
Import OverheadsSbfFifoSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: in the official environment [ideal.processor_state] is also in scope, so the overheads
   processor model prints module-qualified; this shadow reproduces that display (no statement is affected). *)
Module ideal_display. Definition processor_state := tt. End ideal_display. Import ideal_display.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_blackout_bound". Abort.
Check @fifo_blackout_bound.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_blackout_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_ovh_sbf_slow". Abort.
Check @fifo_ovh_sbf_slow.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_ovh_sbf_slow". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_monotone". Abort.
Print statement_overheads_sbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_blackout_bound_monotone". Abort.
Print statement_fifo_blackout_bound_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_blackout_bound_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_unit". Abort.
Print statement_overheads_sbf_unit.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_unit". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_busy_valid". Abort.
Print statement_overheads_sbf_busy_valid.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_busy_valid". Abort.
