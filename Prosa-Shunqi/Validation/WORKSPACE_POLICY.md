# Workspace Isolation Policy

1. `../Prosa-fei/` is the historical workspace and is read-only by default.
2. New production translation code may be written only under
   `Prosa-Shunqi/Prosa/`.
3. Historical Lean code may enter production only through the approved
   migration/reuse workflow and after applying the v0.6 delta.
4. Compiling an old Lean file does not establish that it translates Prosa
   v0.6.
5. Planning artifacts, prototypes, fixtures, imported artifacts, and
   certificates do not count toward production translation coverage.
6. Production coverage counts only accepted declarations under
   `Prosa-Shunqi/Prosa/`.
7. The authoritative source is always Prosa v0.6 commit
   `414e66760333eaa4ef78c685bcf53291c527a548`.

Current Lean and historical Prosa sources are references only and may never
override the pinned v0.6 semantics.
