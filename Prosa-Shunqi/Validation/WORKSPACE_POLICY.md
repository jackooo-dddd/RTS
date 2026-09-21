# Workspace Isolation Policy

1. `../Prosa-fei/` is the historical workspace and is read-only by default.
2. New translation candidates may be written only under
   `Prosa-Shunqi/Prosa/`, the official current v0.6 Lean candidate tree.
3. Historical Lean code may enter production only through the approved
   migration/reuse workflow and after applying the v0.6 delta.
4. Compiling an old Lean file does not establish that it translates Prosa
   v0.6.
5. Planning artifacts, prototypes, fixtures, imported artifacts, and
   certificates do not count toward production translation coverage.
6. A file existing under `Prosa-Shunqi/Prosa/` is not by itself accepted.
   Production coverage counts only declarations marked
   `ACCEPTED_V06_TRANSLATION` in
   `Validation/planning/v06_pipeline/*status.json` and `*manifest.json`.
7. The authoritative source is always Prosa v0.6 commit
   `414e66760333eaa4ef78c685bcf53291c527a548`.
8. File readiness is determined by the authoritative file DAG. Among ready,
   unfinished files, execution follows `../v06_file_translation_order.md`.
9. Each started source file has one canonical report under `../Reports/files/`.
   Its filename begins with the timestamp of the earliest historical report
   for that source file, without a timezone suffix. Later batches and
   revalidation update that same report; legacy date/batch reports are not the
   current status authority.

Current Lean and historical Prosa sources are references only and may never
override the pinned v0.6 semantics.
