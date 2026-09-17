From mathcomp Require Import ssreflect ssrbool ssrnat eqtype fintype.

Example scheduled_exists_forall_mutation_detected :
  (true || false) != (true && false).
Proof. by []. Qed.

Example scheduled_polarity_mutation_detected :
  true != ~~ true.
Proof. by []. Qed.

Example completed_ge_le_mutation_detected : (3 <= 5) != (5 <= 3).
Proof. by []. Qed.

Example completed_ge_gt_mutation_detected :
  (3 <= 3) != (3 < 3).
Proof. by []. Qed.
