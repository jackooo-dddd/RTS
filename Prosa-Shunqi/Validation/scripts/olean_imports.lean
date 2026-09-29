import Lean
open Lean

/-- Print, for each `.olean` path argument, `path<TAB>imported modules` (space separated),
read from the compiled module data itself (not from any source file).  Used by
`translation_file_pipeline.py` to key the fixture cache on the actual import closure. -/
def main (args : List String) : IO Unit := do
  for p in args do
    let (md, _) ← readModuleData p
    IO.println s!"{p}\t{String.intercalate " " (md.imports.toList.map (·.module.toString))}"
