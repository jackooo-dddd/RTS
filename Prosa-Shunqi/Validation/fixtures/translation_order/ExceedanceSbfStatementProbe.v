Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.ExceedanceSbfSemanticSource.
Import ExceedanceSbfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.exceedance.SBF.eps_sbf". Abort.
Check @eps_sbf.
Goal True. idtac "END|prosa.analysis.facts.model.exceedance.SBF.eps_sbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.exceedance.SBF.blackout_during_bounded". Abort.
Print statement_blackout_during_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.exceedance.SBF.blackout_during_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_valid". Abort.
Print statement_eps_sbf_is_valid.
Goal True. idtac "END|prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_unit". Abort.
Print statement_eps_sbf_is_unit.
Goal True. idtac "END|prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_unit". Abort.
