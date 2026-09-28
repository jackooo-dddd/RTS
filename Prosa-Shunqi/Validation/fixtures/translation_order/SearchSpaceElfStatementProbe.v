Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.SearchSpaceElfSemanticSource.
Import SearchSpaceElfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
(* display-only: the imports of the source (ELF/GEL instances, Int notations, the qualified ELF blocking bound) *)
Require Import prosa.util.int prosa.model.priority.gel prosa.model.priority.elf.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.elf.is_in_search_space". Abort.
Check @is_in_search_space.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.elf.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.elf.search_space_sub". Abort.
Print statement_search_space_sub.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.elf.search_space_sub". Abort.
