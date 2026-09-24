From FoundationCertificates Require Import SwapNatEquality SwapCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN nat_equality_dependency".
  Print Assumptions swap_nat_beq_related.
  idtac "AUDIT_END nat_equality_dependency".
  idtac "AUDIT_BEGIN replace_at".
  Print Assumptions replace_at_correspondence.
  idtac "AUDIT_END replace_at".
  idtac "AUDIT_BEGIN swapped".
  Print Assumptions swapped_correspondence.
  idtac "AUDIT_END swapped".
Abort.
