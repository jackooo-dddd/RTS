import path from "path"
import fs from "fs/promises"
import { createHash } from "crypto"
import { Filesystem } from "../util/filesystem"
import { which } from "../util/which"
import { runProcess, type ProcessOptions, type ProcessResult } from "./coq-project"

/** Lake project helpers shared by the Lean tools (lean_check, the final gate, lean_session). */
export namespace LeanProject {
  export const DEFAULT_TIMEOUT_MS = 20 * 60_000

  export type Diagnostic = {
    file: string
    line: number
    column: number
    severity: "error" | "warning" | "info"
    message: string
  }

  /** The nearest directory at or above `start` that holds a Lake project (`lakefile.lean` or `lakefile.toml`). */
  export function findRoot(start: string): string | undefined {
    let dir = path.resolve(start)
    if (Filesystem.stat(dir)?.isFile()) dir = path.dirname(dir)
    while (true) {
      if (Filesystem.stat(path.join(dir, "lakefile.lean")) || Filesystem.stat(path.join(dir, "lakefile.toml"))) return dir
      const parent = path.dirname(dir)
      if (parent === dir) return undefined
      dir = parent
    }
  }

  /** `CaseStudies/ECRTS2005/Lemma3/Solution.lean` → `CaseStudies.ECRTS2005.Lemma3.Solution`. */
  export function moduleName(root: string, file: string) {
    const rel = path.relative(root, path.resolve(file))
    if (rel.startsWith("..") || !rel.endsWith(".lean")) return undefined
    return rel.slice(0, -".lean".length).split(path.sep).join(".")
  }

  export function moduleFile(root: string, module: string) {
    return path.join(root, ...module.split(".")) + ".lean"
  }

  export function lake() {
    return process.env.OPENCODE_LAKE?.trim() || which("lake") || "lake"
  }

  export function timeoutMs() {
    const parsed = Number.parseInt(process.env.OPENCODE_LEAN_TIMEOUT_MS ?? "", 10)
    return Number.isFinite(parsed) && parsed > 0 ? parsed : DEFAULT_TIMEOUT_MS
  }

  /** `lake env lean <file>` in the project root. */
  export function leanFile(root: string, file: string, options: ProcessOptions = {}) {
    return runProcess([lake(), "env", "lean", file], root, { timeoutMs: timeoutMs(), ...options })
  }

  /** `lake build <modules…>` in the project root. */
  export function build(root: string, modules: string[], options: ProcessOptions = {}) {
    return runProcess([lake(), "build", ...modules], root, { timeoutMs: timeoutMs(), ...options })
  }

  /**
   * Elaborate `source` as if it were `file`, without touching `file`: the text is written to a hidden sibling
   * (same directory, so relative tooling behaves the same) and removed afterwards. Diagnostics are reported
   * against `file`.
   */
  export async function checkSource(root: string, file: string, source: string, options: ProcessOptions = {}) {
    const hash = createHash("sha256").update(file + "\n" + source).digest("hex").slice(0, 12)
    const temp = path.join(path.dirname(file), `.LeanBuddyCheck_${hash}.lean`)
    await fs.writeFile(temp, source, "utf8")
    try {
      const result = await leanFile(root, temp, options)
      return { result, diagnostics: parseDiagnostics(result.stdout + "\n" + result.stderr, temp, file) }
    } finally {
      await fs.rm(temp, { force: true })
    }
  }

  const DIAGNOSTIC = /^(.+?):(\d+):(\d+): (error|warning|info)(?:\([^)]*\))?: ?/

  /**
   * Parse `lean` command-line diagnostics (`file:line:col: error: message`, continuation lines indented or
   * following until the next diagnostic). `renameFrom` → `renameTo` maps a temporary file back to the real one.
   */
  export function parseDiagnostics(output: string, renameFrom?: string, renameTo?: string): Diagnostic[] {
    const out: Diagnostic[] = []
    for (const line of output.split("\n")) {
      const match = DIAGNOSTIC.exec(line)
      if (match) {
        let file = match[1]
        if (renameFrom && (file === renameFrom || path.resolve(file) === path.resolve(renameFrom))) file = renameTo ?? file
        out.push({
          file,
          line: Number(match[2]),
          column: Number(match[3]),
          severity: match[4] as Diagnostic["severity"],
          message: line.slice(match[0].length),
        })
        continue
      }
      const last = out.at(-1)
      if (last && line.trim()) last.message += "\n" + line
    }
    return out
  }

  export function failed(result: ProcessResult) {
    return result.exit !== 0 || result.timedOut || result.aborted || result.outputLimitExceeded
  }
}
