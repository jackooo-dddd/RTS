Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FifoFixpointSemanticSource.
Import FifoFixpointSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.analysis.definitions.sbf.pred prosa.model.priority.fifo.
(* display-only: the official environment names the FIFO search space's definition and source-local IBF
   `fifo.is_in_search_space`/`fifo.IBF` and this file's source-local helper `fifo_fixpoint.intra_IBF` *)
Module fifo.
  Notation IBF := prosa.SearchSpaceFifoSemanticSource.SearchSpaceFifoSemanticSource.IBF.
  Notation is_in_search_space := prosa.SearchSpaceFifoSemanticSource.SearchSpaceFifoSemanticSource.is_in_search_space.
End fifo.
Import fifo.
Module fifo_fixpoint.
  Notation intra_IBF := prosa.FifoFixpointSemanticSource.FifoFixpointSemanticSource.intra_IBF.
End fifo_fixpoint.
Import fifo_fixpoint.
Module FifoFixpointProbeDisplay.
  Definition IBF := tt. Definition is_in_search_space := tt. Definition intra_IBF := tt.
End FifoFixpointProbeDisplay.
Import FifoFixpointProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint.soln_abstract_response_time_recurrence". Abort.
Print statement_soln_abstract_response_time_recurrence.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint.soln_abstract_response_time_recurrence". Abort.
