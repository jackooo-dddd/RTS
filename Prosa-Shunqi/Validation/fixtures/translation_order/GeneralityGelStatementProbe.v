Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.GeneralityGelSemanticSource.
Import GeneralityGelSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
(* display-only: the imports of the source (GEL/EDF/FIFO instances, Int notations) *)
Require Import prosa.util.int prosa.model.priority.gel prosa.model.priority.fifo prosa.model.priority.edf prosa.model.task.absolute_deadline.
Goal True. idtac "BEGIN|prosa.results.generality.gel.gel_generalizes_edf". Abort.
Print statement_gel_generalizes_edf.
Goal True. idtac "END|prosa.results.generality.gel.gel_generalizes_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.gel.gel_generalizes_fifo". Abort.
Print statement_gel_generalizes_fifo.
Goal True. idtac "END|prosa.results.generality.gel.gel_generalizes_fifo". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.gel.pp_delta". Abort.
Check @pp_delta.
Goal True. idtac "END|prosa.results.generality.gel.pp_delta". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.gel.backlogged_job_has_lower_gel_prio". Abort.
Print statement_backlogged_job_has_lower_gel_prio.
Goal True. idtac "END|prosa.results.generality.gel.backlogged_job_has_lower_gel_prio". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.gel.gel_conditionally_generalizes_fp". Abort.
Print statement_gel_conditionally_generalizes_fp.
Goal True. idtac "END|prosa.results.generality.gel.gel_conditionally_generalizes_fp". Abort.
