Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.SearchSpaceFpSemanticSource.
Import SearchSpaceFpSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.util.epsilon prosa.util.rel prosa.model.task.concept prosa.model.task.arrival.curves prosa.model.priority.classes.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.fp.is_in_search_space". Abort.
Check @is_in_search_space.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.fp.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.fp.search_space_sub". Abort.
Print statement_search_space_sub.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.fp.search_space_sub". Abort.
