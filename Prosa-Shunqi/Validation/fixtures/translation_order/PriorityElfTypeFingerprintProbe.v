(* Recomputes the authoritative `Check @name` fingerprints for model/priority/elf.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.model.priority.elf.
Goal True. idtac "BEGIN|prosa.model.priority.elf.ELF". Abort.
Check @prosa.model.priority.elf.ELF.
Goal True. idtac "END|prosa.model.priority.elf.ELF". Abort.
