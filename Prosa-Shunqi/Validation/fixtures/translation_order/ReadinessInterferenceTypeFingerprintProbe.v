(* Recomputes the authoritative `Check @name` fingerprints for readiness_interference.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.analysis.definitions.readiness_interference.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness_interference.some_hep_job_ready". Abort.
Check @prosa.analysis.definitions.readiness_interference.some_hep_job_ready.
Goal True. idtac "END|prosa.analysis.definitions.readiness_interference.some_hep_job_ready". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness_interference.cumulative_readiness_interference". Abort.
Check @prosa.analysis.definitions.readiness_interference.cumulative_readiness_interference.
Goal True. idtac "END|prosa.analysis.definitions.readiness_interference.cumulative_readiness_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness_interference.readiness_interference_is_bounded". Abort.
Check @prosa.analysis.definitions.readiness_interference.readiness_interference_is_bounded.
Goal True. idtac "END|prosa.analysis.definitions.readiness_interference.readiness_interference_is_bounded". Abort.
