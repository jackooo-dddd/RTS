Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.SearchSpaceFifoSemanticSource.
Import SearchSpaceFifoSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
(* display-only: the imports of the source *)
Require Import prosa.analysis.definitions.sbf.pred.
(* display-only: the official environment names the source-local IBF of this file as `fifo.IBF` *)
Module fifo.
  Notation IBF := prosa.SearchSpaceFifoSemanticSource.SearchSpaceFifoSemanticSource.IBF.
End fifo.
Import fifo.
Module SearchSpaceFifoProbeDisplay. Definition IBF := tt. End SearchSpaceFifoProbeDisplay.
Import SearchSpaceFifoProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.fifo.is_in_search_space". Abort.
Check @is_in_search_space.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.fifo.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.fifo.search_space_sub". Abort.
Print statement_search_space_sub.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.fifo.search_space_sub". Abort.
