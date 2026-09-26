(* Recomputes the authoritative `Check @name` fingerprints for analysis/definitions/delay_propagation.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.analysis.definitions.delay_propagation.
(* display-only: the authoritative evidence was printed with the ssrfun
   notation [f^~ y] in scope and with [id] naming Datatypes.id *)
From mathcomp Require Import ssrfun.
Import Corelib.Init.Datatypes.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.valid_delay_propagation_mapping". Abort.
Check @prosa.analysis.definitions.delay_propagation.valid_delay_propagation_mapping.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.valid_delay_propagation_mapping". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.propagated_arrival_sequence". Abort.
Check @prosa.analysis.definitions.delay_propagation.propagated_arrival_sequence.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.propagated_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.job_mapping_uniq". Abort.
Check @prosa.analysis.definitions.delay_propagation.job_mapping_uniq.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.job_mapping_uniq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.valid_arr_seq_propagation_mapping". Abort.
Check @prosa.analysis.definitions.delay_propagation.valid_arr_seq_propagation_mapping.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.valid_arr_seq_propagation_mapping". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.jitter_delay_mapping_valid". Abort.
Check @prosa.analysis.definitions.delay_propagation.jitter_delay_mapping_valid.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.jitter_delay_mapping_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.release_sequence". Abort.
Check @prosa.analysis.definitions.delay_propagation.release_sequence.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.release_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.jitter_arr_seq_mapping_valid". Abort.
Check @prosa.analysis.definitions.delay_propagation.jitter_arr_seq_mapping_valid.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.jitter_arr_seq_mapping_valid". Abort.
Check @prosa.analysis.definitions.delay_propagation.release_as_arrival.
Print prosa.analysis.definitions.delay_propagation.release_as_arrival.
