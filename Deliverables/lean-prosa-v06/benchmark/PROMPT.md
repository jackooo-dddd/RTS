# Prompt template

You are working in the Lean 4 package `lean-prosa-v06` (Lean v4.33.1, Mathlib), which contains a Lean version
of the real-time scheduling library Prosa (`Prosa.*`, including classic Prosa under `Prosa.Classic.*`).

Task `{TASK_ID}` ({PAPER}): prove the proposition `{STATEMENT}`, defined in `{STATEMENT_FILE}`.

Write your proof in `{SOLUTION_FILE}` by replacing the `sorry` in

    theorem solution : ... := by
      sorry

Rules:
- Do not change the name or the type of `solution`, and do not edit any file outside `Solutions/`.
- You may add imports of modules of this package (`Prosa.*`, `Mathlib.*`), helper lemmas and definitions,
  and new files under `Solutions/`.
- No `sorry`, `admit`, new axioms, `native_decide`, or meta-programming (`#eval`, `run_cmd`, `elab`, ...).
- Build with `lake build {SOLUTION_MODULE}`; the final check is `python3 benchmark/check.py {TASK_ID}`.
