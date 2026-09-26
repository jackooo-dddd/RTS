Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BlockingBoundFpSemanticSource.
Import BlockingBoundFpSemanticSource.
Goal True. idtac "BEGIN|prosa.analysis.definitions.blocking_bound.fp.blocking_bound". Abort.
Check @blocking_bound.
Goal True. idtac "END|prosa.analysis.definitions.blocking_bound.fp.blocking_bound". Abort.
