# Prompt template

You are working in the Lean 4 package `lean-prosa-v06` (Lean v4.33.1, Mathlib), which contains a Lean version
of the real-time scheduling library Prosa (`Prosa.*`, including classic Prosa under `Prosa.Classic.*`).

Task `{TASK_ID}` ({PAPER}): prove the proposition `{STATEMENT}`, defined in `{STATEMENT_FILE}`.
The task folder `{FOLDER}` also contains `proof.tex`, the paper's statement and proof sketch in LaTeX, as a
hint (omit this sentence when `hint_file` is `null`).

Write your proof in `{SOLUTION_FILE}` by replacing the `sorry` in

    theorem solution : ... := by
      sorry

Rules:
- Do not change the name or the type of `solution`. Do not edit `Statement.lean`, `proof.tex`, or any file
  outside `CaseStudies/`.
- You may add imports of modules of this package (`Prosa.*`, `Mathlib.*`), helper lemmas and definitions,
  and new `.lean` files under `CaseStudies/`.
- No `sorry`, `admit`, new axioms, `native_decide`, or meta-programming (`#eval`, `run_cmd`, `elab`, ...).
- Build with `lake build {SOLUTION_MODULE}`; the final check is `python3 benchmark/check.py {TASK_ID}`.
