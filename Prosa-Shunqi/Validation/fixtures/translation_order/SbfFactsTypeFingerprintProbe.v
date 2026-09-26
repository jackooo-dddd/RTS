(* Recomputes the authoritative `Check @name` fingerprints for analysis/facts/SBF.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.analysis.facts.SBF.
Goal True. idtac "BEGIN|prosa.analysis.facts.SBF.valid_pred_sbf_switch_predicate". Abort.
Check @prosa.analysis.facts.SBF.valid_pred_sbf_switch_predicate.
Goal True. idtac "END|prosa.analysis.facts.SBF.valid_pred_sbf_switch_predicate". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.SBF.blackout_during_bound_SBF". Abort.
Check @prosa.analysis.facts.SBF.blackout_during_bound_SBF.
Goal True. idtac "END|prosa.analysis.facts.SBF.blackout_during_bound_SBF". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.SBF.complement_SBF_monotone". Abort.
Check @prosa.analysis.facts.SBF.complement_SBF_monotone.
Goal True. idtac "END|prosa.analysis.facts.SBF.complement_SBF_monotone". Abort.
