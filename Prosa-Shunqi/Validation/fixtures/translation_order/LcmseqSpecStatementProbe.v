Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.LcmseqSemanticSource.
Import LcmseqSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Goal True. idtac "BEGIN|prosa.util.lcmseq.lcml". Abort.
Check @lcml.
Goal True. idtac "END|prosa.util.lcmseq.lcml". Abort.
Goal True. idtac "BEGIN|prosa.util.lcmseq.int_divides_lcm_in_seq". Abort.
Print statement_int_divides_lcm_in_seq.
Goal True. idtac "END|prosa.util.lcmseq.int_divides_lcm_in_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.lcmseq.lcm_seq_divides_lcm_super". Abort.
Print statement_lcm_seq_divides_lcm_super.
Goal True. idtac "END|prosa.util.lcmseq.lcm_seq_divides_lcm_super". Abort.
Goal True. idtac "BEGIN|prosa.util.lcmseq.lcm_seq_is_mult_of_all_ints". Abort.
Print statement_lcm_seq_is_mult_of_all_ints.
Goal True. idtac "END|prosa.util.lcmseq.lcm_seq_is_mult_of_all_ints". Abort.
Goal True. idtac "BEGIN|prosa.util.lcmseq.all_pos_implies_lcml_pos". Abort.
Print statement_all_pos_implies_lcml_pos.
Goal True. idtac "END|prosa.util.lcmseq.all_pos_implies_lcml_pos". Abort.
