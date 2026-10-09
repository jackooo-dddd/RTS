import { LeanSource } from "@/tool/lean-source"

/**
 * Lean source primitives for the proof workflow (tools-advices proof-workflow-revision.md §1–§5): comment masking,
 * theorem spans, unfinished-proof placeholders, region markers and contract comments in Lean syntax.
 *
 * Lean has no `Proof.`/`Qed.` pair: a theorem's proof is the text after the `:=` of its declaration up to the next
 * top-level command, and "unfinished" means a `sorry` (or `admit`) is left in it. Empty `()`/`{}` are not proof holes
 * (prompt_revision.md §0.1).
 */
export namespace LeanProofSource {
  /** `sorry`/`admit` placeholders in masked text. */
  export const PENDING_PLACEHOLDER = /\b(?:sorry|admit)\b/
  export const PENDING_PLACEHOLDER_GLOBAL = /\b(?:sorry|admit)\b/g
  /** Lean has no empty-block proof holes; kept as a never-matching pattern so callers stay uniform. */
  export const EMPTY_PROOF_BLOCK = /(?!)/
  export const EMPTY_PROOF_BLOCK_GLOBAL = /(?!)/g
  export const UNFINISHED_PROOF = /\b(?:sorry|admit)\b/
  export const INFORMAL_PROOF_COMMENT = /(?:\/-[\s\S]*?\binformal proof\b[\s\S]*?-\/|--[^\n]*\binformal proof\b)/i
  /** Region markers: block comments (`/- proof_region begin … -/`) or line comments (`-- proof_region begin …`). */
  export const REGION_BEGIN = /(?:\/-\s*proof_region\s+begin\s+([\s\S]*?)\s*-\/|--[ \t]*proof_region[ \t]+begin[ \t]+([^\n]*))/g
  export const REGION_END = /(?:\/-\s*proof_region\s+end(?:\s+admit_id:\s*(\S+?))?\s*-\/|--[ \t]*proof_region[ \t]+end(?:[ \t]+admit_id:[ \t]*(\S+))?[^\n]*)/g

  /** Attribute text of a REGION_BEGIN match / admit_id of a REGION_END match (whichever alternative matched). */
  export function beginAttributes(match: RegExpExecArray | RegExpMatchArray) {
    return match[1] ?? match[2] ?? ""
  }
  export function endAdmitID(match: RegExpExecArray | RegExpMatchArray) {
    return match[1] ?? match[2]
  }

  /**
   * Replace comments, string literals and character literals by spaces (same length, newlines kept). Returns
   * undefined for an unterminated block comment or string, like the former Coq masker.
   */
  export function maskCommentsAndStrings(source: string) {
    const out = source.split("")
    let i = 0
    while (i < source.length) {
      if (source.startsWith("--", i)) {
        while (i < source.length && source[i] !== "\n") out[i++] = " "
        continue
      }
      if (source.startsWith("/-", i)) {
        let depth = 0
        while (i < source.length) {
          if (source.startsWith("/-", i)) {
            depth++
            out[i] = out[i + 1] = " "
            i += 2
          } else if (source.startsWith("-/", i)) {
            depth--
            out[i] = out[i + 1] = " "
            i += 2
            if (!depth) break
          } else {
            if (source[i] !== "\n" && source[i] !== "\r") out[i] = " "
            i++
          }
        }
        if (depth) return undefined
        continue
      }
      if (source[i] === '"') {
        out[i++] = " "
        let closed = false
        while (i < source.length) {
          if (source[i] === "\\") {
            out[i] = " "
            if (i + 1 < source.length && source[i + 1] !== "\n") out[i + 1] = " "
            i += 2
            continue
          }
          if (source[i] === '"') {
            out[i++] = " "
            closed = true
            break
          }
          if (source[i] !== "\n" && source[i] !== "\r") out[i] = " "
          i++
        }
        if (!closed) return undefined
        continue
      }
      if (source[i] === "'" && (i === 0 || !/[\p{L}\p{N}_'!?]/u.test(source[i - 1]))) {
        const close = source[i + 1] === "\\" ? i + 3 : i + 2
        if (source[close] === "'") {
          for (let j = i; j <= close; j++) out[j] = " "
          i = close + 1
          continue
        }
      }
      i++
    }
    return out.join("")
  }

  export type TheoremSpan = {
    name: string
    start: number
    end: number
    /** Offset of the `:=` of the declaration. */
    assign?: number
    /** Offset where the proof body starts (after `:= by`, or after `:=` for a term proof). */
    proofStart?: number
    /** Offset just past the proof body (the declaration's end without trailing whitespace). */
    proofEnd?: number
    rootGoal?: string
  }

  /** `theorem`/`lemma` declarations with their proof spans. */
  export function theoremSpans(source: string): TheoremSpan[] {
    return LeanSource.declarations(source)
      .filter((decl) => decl.keyword === "theorem" || decl.keyword === "lemma")
      .map((decl) => {
        if (decl.assign === undefined) return { name: decl.name, start: decl.start, end: decl.end }
        const after = /^:=\s*(?:by\b)?/.exec(source.slice(decl.assign))
        const proofStart = decl.assign + (after?.[0].length ?? 2)
        const proofEnd = proofStart + source.slice(proofStart, decl.end).replace(/\s+$/, "").length
        return {
          name: decl.name,
          start: decl.start,
          end: decl.end,
          assign: decl.assign,
          proofStart,
          proofEnd,
          rootGoal: LeanSource.binderSignatureAsType(decl.signature),
        }
      })
  }

  /** Unqualified name of a declaration name (`CaseStudies.X.solution` → `solution`). */
  export function shortName(name: string) {
    return name.split(".").at(-1) ?? name
  }

  /** Lines that start a top-level command (would leave the theorem's proof if they appeared in it). */
  export function topLevelCommandLine(maskedProof: string) {
    return maskedProof
      .split("\n")
      .findIndex((line) => /^(?:theorem|lemma|def|abbrev|example|instance|structure|class|inductive|axiom|opaque|namespace|section|end|open|variable|universe|set_option|attribute|import|@\[|#)\b/.test(line))
  }

  /** Lean comments (block `/- -/` and runs of `--` lines) that end before `limit`, newest first. */
  export function commentsBefore(source: string, limit: number) {
    const window = source.slice(Math.max(0, limit - 2400), limit)
    const out: string[] = []
    for (const m of window.matchAll(/\/-([\s\S]*?)-\//g)) out.push(m[1])
    const lineRun = /(?:^[ \t]*--[^\n]*\n?)+/gm
    for (const m of window.matchAll(lineRun)) out.push(m[0].replace(/^[ \t]*--/gm, ""))
    return out.reverse()
  }

  /**
   * Leading contract comments right after a region's begin marker: consecutive `/- … -/` blocks or `--` lines;
   * once Lean code starts, later comments are proof comments, not scheduler metadata.
   */
  export function leadingComments(text: string) {
    const comments: string[] = []
    let offset = 0
    while (offset < text.length) {
      offset += /^\s*/.exec(text.slice(offset))?.[0].length ?? 0
      if (text.startsWith("/-", offset)) {
        const end = text.indexOf("-/", offset + 2)
        if (end < 0) break
        comments.push(text.slice(offset + 2, end))
        offset = end + 2
        continue
      }
      if (text.startsWith("--", offset)) {
        const end = text.indexOf("\n", offset)
        comments.push(text.slice(offset + 2, end < 0 ? text.length : end))
        offset = end < 0 ? text.length : end + 1
        continue
      }
      break
    }
    return comments
  }

  /** Local `have`/`suffices` declarations with their propositions (Lean syntax, up to `:=` at depth 0). */
  export function targetDeclarations(blockText: string) {
    const masked = maskCommentsAndStrings(blockText) ?? blockText
    const out: { name: string; statement: string; proposition: string }[] = []
    const re = /\b(?:have|suffices|show)\s+([^\s:(⟨]+)\s*:/g
    for (let m: RegExpExecArray | null; (m = re.exec(masked)); ) {
      const name = m[1]
      let depth = 0
      let end = -1
      for (let i = m.index + m[0].length; i < masked.length - 1; i++) {
        const c = masked[i]
        if ("([{⟨⦃".includes(c)) depth++
        else if (")]}⟩⦄".includes(c)) depth--
        else if (depth === 0 && c === ":" && masked[i + 1] === "=") {
          end = i
          break
        }
        if (depth < 0) break
      }
      if (end < 0) continue
      const statement = blockText.slice(m.index, end).trim()
      const proposition = blockText.slice(m.index + m[0].length, end).replace(/\s+/g, " ").trim()
      out.push({ name, statement, proposition })
    }
    return out
  }

  /**
   * K1: added `import` lines of package modules are allowed in the protected header. Returns `after` with those added
   * import lines removed (so the remaining text can be compared with the protected prefix), or undefined when an added
   * import is not a package module.
   */
  export function stripAllowedAddedImports(after: string, original: string) {
    const before = new Set(LeanSource.header(original).imports)
    const header = LeanSource.header(after)
    const roots = LeanSource.importRoots()
    const added = header.imports.filter((m) => !before.has(m))
    if (added.some((m) => !roots.some((root) => m === root || m.startsWith(root + ".")))) return undefined
    if (!added.length) return after
    const headText = after.slice(0, header.bodyOffset)
    const kept = headText
      .split("\n")
      .filter((line) => {
        const imp = /^\s*import\s+(.*)$/.exec(line)
        if (!imp) return true
        const modules = imp[1].replace(/--.*$/, "").trim().split(/\s+/)
        return !modules.every((m) => added.includes(m))
      })
      .join("\n")
    return kept + after.slice(header.bodyOffset)
  }
}
