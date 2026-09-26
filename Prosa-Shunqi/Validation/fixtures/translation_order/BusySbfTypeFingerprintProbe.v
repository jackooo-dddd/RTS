(* Recomputes the authoritative `Check @name` fingerprints for busy_sbf.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.analysis.abstract.restricted_supply.busy_sbf.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.busy_sbf.sbf_respected_in_busy_interval". Abort.
Check @prosa.analysis.abstract.restricted_supply.busy_sbf.sbf_respected_in_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.busy_sbf.sbf_respected_in_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.busy_sbf.valid_busy_sbf". Abort.
Check @prosa.analysis.abstract.restricted_supply.busy_sbf.valid_busy_sbf.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.busy_sbf.valid_busy_sbf". Abort.
