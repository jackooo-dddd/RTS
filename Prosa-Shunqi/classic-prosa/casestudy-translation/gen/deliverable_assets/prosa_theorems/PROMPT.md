You are working in a Lean 4 project (Lean `v4.33.1`, Mathlib) that contains a Lean version of the Prosa library
for real-time scheduling theory.

Prove the theorem `{lean_declaration}` in `{lean_file}`. Its proof is currently `sorry`. The statement is:

```lean
{statement}
```

Rules:
- Edit only the proof of this theorem (the text after its `:=`). Do not change its statement, the rest of the
  file, or any other file. Put any helper lemmas inside the proof (`have`).
- You may use everything the file can see: its imports (Mathlib and the Prosa modules it imports) and the
  declarations above the theorem in the same file.
- Do not use `sorry`, `admit`, new axioms, `native_decide`, or meta-programming escapes. The proof may depend
  only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
- Check your work with `lake build {lean_module}`.
