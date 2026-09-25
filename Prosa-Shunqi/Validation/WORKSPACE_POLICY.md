# Workspace Isolation Policy

1. Other workspaces are read-only by default and are not translation memory
   for this v0.6 project.
2. New translation candidates may be written only under
   `Prosa-Shunqi/Prosa/`, the official current v0.6 Lean candidate tree.
3. New translation candidates come from the pinned v0.6 source and approved
   representation policy; previously accepted v0.6 declarations and bridges
   may be reused with their evidence checks.
4. Compiling a Lean file alone does not establish v0.6 semantic acceptance.
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

No other source version may override the pinned v0.6 semantics.
