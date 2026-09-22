(** Validation-only Rocq 9.3 compatibility interface used to compile the
    byte-identical official [behavior/arrival_sequence.v] dependency chain.

    Compared with the Job-only surface, ArrivalSequence additionally observes
    MathComp [seq] through the [JobType] boundary.  This file exports only the
    external libraries needed by the exact source files and declares no Prosa
    symbol.  It is not a replacement source model. *)
From mathcomp Require Export ssreflect ssrnat ssrbool eqtype seq fintype bigop.

Require Export mathcomp.zify.zify.
