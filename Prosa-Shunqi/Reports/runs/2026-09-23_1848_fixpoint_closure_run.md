# Fixpoint closure run — 2026-09-23 18:48

The authoritative `util/fixpoint.v` at Prosa v0.6 commit
`414e66760333eaa4ef78c685bcf53291c527a548` is now an
`ACCEPTED_V06_FILE`: all 17 declarations have proof-clean Lean counterparts
and fresh actual-artifact Rocq semantic certificates. Four computational
definitions are `CERTIFIED`; 13 theorem statements are
`CERTIFIED_WITH_PROP_SPROP_FOUNDATION`. No certificate has an unclosed
semantic premise, source/target theorem self-dependency, transitive
statement-only theorem dependency, or unexpected assumption. The sole
non-importer theorem-level trust component is the previously approved
`PropSPropFoundation.interpret_strict`.

The isolated `CLEAN_FULL` run rebuilt nine Lean modules, re-extracted the
official source signatures, exported the compiled Fixpoint interface,
re-imported it into Rocq 9.3, recompiled the correspondence DAG, and passed
the fail-closed Lean `#print axioms` and Rocq `Print Assumptions` audits.
Initial successful snapshot: `68f73afe00f5cb327e6ec68e78319502676719dcbdd0602b0400048f307e3bb7`.
The [canonical file report](../files/util/2026-09-23_150425_fixpoint.md)
records the full declaration history and artifact hashes; the
[manifest](../../Validation/planning/v06_pipeline/util_fixpoint_module_manifest.json)
and [status](../../Validation/planning/v06_pipeline/util_fixpoint_module_status.json)
are machine authority.

Measured fresh Lean build time was 51.86 seconds: Fixpoint itself took 5.82
seconds and eight dependency modules 46.05 seconds (89%). Source acquisition,
export, import, certificate compilation, and publication were not timed
individually in this file-specific run, so no breakdown is inferred for them.
An initial attempt stopped after a successful Lean build because macOS Bash
does not provide `mapfile`; the script was corrected and the successful run
rebuilt afresh. This did not affect the semantic result.

Coverage moved from 29/357 files and 252/2439 declarations to **30/357**
and **269/2439**. `util/lcmseq.v` remains a separate unfinished rank-30
file; this run did not certify it or change `Prosa-fei/`.

Reproduce with `cd Prosa-Shunqi && bash Validation/scripts/validate_utility_fixpoint.sh`.

At 18:55 the one-command run was repeated after tightening the prepare input
fingerprint to include the validator and source-extraction tooling. It passed
again and superseded the initial publication with snapshot
`f6f850c6e1a01e93840114108b64791889eb9b74a22fcecd4fab6d637d7bb5a4`.
The final run's measured Lean build time was 46.28 seconds (Fixpoint 5.78,
dependencies 40.50); certificate statuses and cumulative coverage did not
change. The machine manifest now points to this final snapshot.
