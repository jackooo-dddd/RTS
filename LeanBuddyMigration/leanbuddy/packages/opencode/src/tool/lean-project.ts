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

  /**
   * `lake env lean --json <file>` in the project root. `--json` prints every message (including `#check`, `trace`
   * and `#print axioms` output, which plain `lean` prints without a position) as one JSON object per line.
   */
  export function leanFile(root: string, file: string, options: ProcessOptions = {}) {
    return runProcess([lake(), "env", "lean", "--json", file], root, { timeoutMs: timeoutMs(), ...options })
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

  type JsonMessage = { fileName?: string; pos?: { line: number; column: number }; severity?: string; data?: string; kind?: string }

  /**
   * Parse `lean --json` messages (one JSON object per line) and, as a fallback, plain `lean` diagnostics
   * (`file:line:col: error: message`, continuation lines until the next diagnostic). `renameFrom` → `renameTo` maps a
   * temporary file back to the real one.
   */
  export function parseDiagnostics(output: string, renameFrom?: string, renameTo?: string): Diagnostic[] {
    const out: Diagnostic[] = []
    const rename = (file: string) =>
      renameFrom && (file === renameFrom || path.resolve(file) === path.resolve(renameFrom) || path.basename(file) === path.basename(renameFrom))
        ? (renameTo ?? file)
        : file
    for (const line of output.split("\n")) {
      if (line.startsWith("{") && line.includes('"severity"')) {
        try {
          const message = JSON.parse(line) as JsonMessage
          out.push({
            file: rename(message.fileName ?? ""),
            line: message.pos?.line ?? 0,
            column: message.pos?.column ?? 0,
            severity: message.severity === "error" ? "error" : message.severity === "warning" ? "warning" : "info",
            message: message.data ?? "",
          })
          continue
        } catch {
          // not a message object; fall through to the text parser
        }
      }
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

  export type CompileResult = {
    ok: boolean
    errors: Diagnostic[]
    warnings: Diagnostic[]
    /** `declaration uses 'sorry'` warnings (unfinished proofs). */
    sorries: Diagnostic[]
    timedOut: boolean
    aborted: boolean
    outputLimitExceeded: boolean
    /** Helper modules that had to be rebuilt first, and that build's failure output if any. */
    helpers: string[]
    helperFailure?: string
    output: string
  }

  /**
   * Check `source` as the content of `file` (the staged revision; the disk file is never touched): first `lake build`
   * the project modules it imports that live next to it under `CaseStudies/` (helper modules the agent may write; a
   * no-op when up to date), then `lake env lean` on a temporary sibling copy.
   */
  export async function compile(file: string, source: string, options: ProcessOptions = {}): Promise<CompileResult> {
    const root = findRoot(file)
    if (!root) throw new Error(`no Lake project contains ${file}`)
    const own = moduleName(root, file)
    const helpers = [...source.matchAll(/^import\s+(CaseStudies\.[^\s]+)/gm)]
      .map((m) => m[1])
      .filter((m) => m !== own && !/\.Statement$/.test(m) && Filesystem.stat(moduleFile(root, m)))
    const empty = { errors: [], warnings: [], sorries: [], timedOut: false, aborted: false, outputLimitExceeded: false }
    if (helpers.length) {
      const built = await build(root, helpers, options)
      if (failed(built)) {
        const output = (built.stdout + "\n" + built.stderr).trim()
        return {
          ...empty,
          ok: false,
          errors: parseDiagnostics(output).filter((d) => d.severity === "error"),
          timedOut: built.timedOut,
          aborted: built.aborted,
          outputLimitExceeded: built.outputLimitExceeded,
          helpers,
          helperFailure: output.slice(-4000),
          output,
        }
      }
    }
    const { result, diagnostics } = await checkSource(root, file, source, options)
    const errors = diagnostics.filter((d) => d.severity === "error")
    const warnings = diagnostics.filter((d) => d.severity === "warning")
    // plain-text output for logs and for messages that are not attached to the file (e.g. lake errors)
    const plain = diagnostics.map((d) => `${path.basename(file)}:${d.line}:${d.column}: ${d.severity}: ${d.message}`).join("\n")
    return {
      ok: !failed(result) && errors.length === 0,
      errors,
      warnings,
      sorries: warnings.filter((d) => /declaration uses [`']sorry[`']/.test(d.message)),
      timedOut: result.timedOut,
      aborted: result.aborted,
      outputLimitExceeded: result.outputLimitExceeded,
      helpers,
      output: plain || (result.stdout + "\n" + result.stderr).trim(),
    }
  }

  export function failed(result: ProcessResult) {
    return result.exit !== 0 || result.timedOut || result.aborted || result.outputLimitExceeded
  }
}
