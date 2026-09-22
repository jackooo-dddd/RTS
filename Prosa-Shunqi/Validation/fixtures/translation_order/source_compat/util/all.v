(** Validation-only Rocq 9.3 compatibility interface for [prosa.util.all].

    The authoritative [behavior/job.v] uses [Require Export prosa.util.all],
    but its five declarations only require the external MathComp exports below.
    Loading the complete historical utility closure on Rocq 9.3 can overflow the
    parser/elaborator stack in [util/list.v].  This file intentionally declares
    no Prosa symbol and must never be treated as source translation evidence.
    The Job validator separately copies [behavior/time.v] and [behavior/job.v]
    byte-for-byte from the pinned v0.6 checkout and audits their hashes/types. *)
From mathcomp Require Export ssreflect ssrnat ssrbool eqtype fintype bigop.

Require Export mathcomp.zify.zify.
