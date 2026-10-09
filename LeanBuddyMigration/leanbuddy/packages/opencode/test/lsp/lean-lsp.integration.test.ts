import { describe, expect, test } from "bun:test"
import path from "path"
import { createHash } from "crypto"
import { LSP } from "../../src/lsp"
import { Instance } from "../../src/project/instance"
import { tmpdir } from "../fixture/fixture"

// DECISIONS D3: the Lean server (`lake serve`) gives diagnostics; S25: they are tagged with the source they belong to.
describe.skipIf(!Bun.which("lake"))("lsp: Lean server", () => {
  test("reports diagnostics for a .lean file and the source hash they were computed for", async () => {
    await using tmp = await tmpdir({ git: true })
    await Bun.write(path.join(tmp.path, "lakefile.lean"), "import Lake\nopen Lake DSL\npackage lsp_test\n")
    await Bun.write(path.join(tmp.path, "lean-toolchain"), "leanprover/lean4:v4.33.1\n")
    const file = path.join(tmp.path, "Demo.lean")
    const source = "theorem demo : 1 + 1 = 3 := by\n  decide\n"
    await Bun.write(file, source)
    await Instance.provide({
      directory: tmp.path,
      fn: async () => {
        expect(await LSP.hasClients(file)).toBe(true)
        await LSP.touchFile(file, true)
        let errors: unknown[] = []
        for (let i = 0; i < 60 && errors.length === 0; i++) {
          errors = ((await LSP.diagnostics())[file] ?? []).filter((d) => (d.severity ?? 1) === 1)
          if (errors.length === 0) await Bun.sleep(500)
        }
        expect(errors.length).toBeGreaterThan(0)
        expect(await LSP.diagnosticsSourceHash(file)).toBe(createHash("sha256").update(source).digest("hex"))
        const status = await LSP.status()
        expect(status.find((entry) => entry.id === "lean")?.lean).toBeDefined()
      },
    })
  }, 120000)
})
