/**
 * Text-level helpers for Lean source files: comment stripping, the forbidden-token scan, the import header and
 * top-level declaration ranges. The comment stripper and the token list are kept identical to the benchmark's
 * `benchmark/check.py` so the agent's gate and the benchmark agree (DECISIONS D4, KNOWN_PROBLEMS K9).
 */
export namespace LeanSource {
  /** Same patterns as `FORBIDDEN` in `benchmark/check.py`. */
  export const FORBIDDEN = [
    /\bsorry\b/g,
    /\badmit\b/g,
    /\baxiom\b/g,
    /\bunsafe\b/g,
    /\bimplemented_by\b/g,
    /@\[extern/g,
    /\bskipKernelTC\b/g,
    /\baddDeclWithoutChecking\b/g,
    /\bset_option\s+debug\./g,
    /\brun_cmd\b/g,
    /\brun_elab\b/g,
    /\brun_meta\b/g,
    /#eval\b/g,
    /\binitialize\b/g,
    /\belab\b/g,
    /\belab_rules\b/g,
  ]

  export const ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]

  /**
   * Remove `-- …` line comments and nested `/- … -/` block comments (including doc comments), exactly as
   * `strip_comments` in `benchmark/check.py` does. String literals are not special-cased there either.
   */
  export function stripComments(text: string) {
    let out = ""
    let i = 0
    let depth = 0
    while (i < text.length) {
      if (text.startsWith("/-", i)) {
        depth++
        i += 2
        continue
      }
      if (depth && text.startsWith("-/", i)) {
        depth--
        i += 2
        continue
      }
      if (depth) {
        i++
        continue
      }
      if (text.startsWith("--", i)) {
        const j = text.indexOf("\n", i)
        i = j < 0 ? text.length : j
        continue
      }
      out += text[i]
      i++
    }
    return out
  }

  /** Forbidden tokens in `text` (comments ignored), sorted and de-duplicated; `allow` drops tokens such as `sorry`. */
  export function forbiddenTokens(text: string, allow: string[] = []) {
    const code = stripComments(text)
    const hits = new Set<string>()
    for (const pattern of FORBIDDEN) {
      for (const match of code.matchAll(pattern)) hits.add(match[0])
    }
    return [...hits].filter((hit) => !allow.includes(hit)).sort()
  }

  export type Header = {
    /** Imported modules, in order. */
    imports: string[]
    /** Character offset where the body (the first non-header command) starts. */
    bodyOffset: number
    /** Number of lines before the body (the line offset of body positions). */
    bodyLine: number
  }

  /** The import header: leading blank lines, comments, an optional `prelude`/`module`, and `import` commands. */
  export function header(source: string): Header {
    const imports: string[] = []
    let i = 0
    let bodyOffset = 0
    while (i < source.length) {
      const rest = source.slice(i)
      const ws = /^\s+/.exec(rest)
      if (ws) {
        i += ws[0].length
        continue
      }
      if (rest.startsWith("--")) {
        const j = source.indexOf("\n", i)
        i = j < 0 ? source.length : j + 1
        continue
      }
      if (rest.startsWith("/-") && !rest.startsWith("/-!") && !rest.startsWith("/--")) {
        // ordinary block comment (nested)
        let depth = 0
        let j = i
        while (j < source.length) {
          if (source.startsWith("/-", j)) {
            depth++
            j += 2
          } else if (source.startsWith("-/", j)) {
            depth--
            j += 2
            if (!depth) break
          } else j++
        }
        i = j
        continue
      }
      const imp = /^(?:(?:public|private|meta)\s+)*import\s+([^\n]*)/.exec(rest)
      if (imp) {
        imports.push(...imp[1].replace(/--.*$/, "").trim().split(/\s+/).filter(Boolean))
        i += imp[0].length
        bodyOffset = i
        continue
      }
      const pre = /^(?:prelude|module)\b/.exec(rest)
      if (pre) {
        i += pre[0].length
        bodyOffset = i
        continue
      }
      break
    }
    // the body starts at the beginning of the line after the last header command
    const nl = source.indexOf("\n", bodyOffset)
    const start = imports.length ? (nl < 0 ? source.length : nl + 1) : 0
    return { imports, bodyOffset: start, bodyLine: source.slice(0, start).split("\n").length - 1 }
  }

  export type Declaration = {
    name: string
    keyword: string
    /** Offset of the declaration's first line (including modifiers/attributes on that line). */
    start: number
    /** Offset just past the declaration (start of the next top-level command, or end of file). */
    end: number
    /** Offset of the `:=` that starts the proof/value, if found at bracket depth 0. */
    assign?: number
    /** The text between the name and `:=` (binders and type). */
    signature: string
  }

  const TOP_LEVEL = /^(?:@\[|\/--|\/-!|#|theorem\b|lemma\b|def\b|abbrev\b|example\b|instance\b|structure\b|class\b|inductive\b|axiom\b|opaque\b|noncomputable\b|private\b|protected\b|partial\b|unsafe\b|namespace\b|section\b|end\b|open\b|variable\b|universe\b|set_option\b|attribute\b|macro\b|syntax\b|notation\b|infix\b|infixl\b|infixr\b|prefix\b|postfix\b|elab\b|deriving\b|mutual\b|local\b|scoped\b|export\b|omit\b|include\b|alias\b|initialize\b)/

  /** Top-level declarations named by `theorem|lemma|def|abbrev|instance` (name as written, possibly qualified). */
  export function declarations(source: string): Declaration[] {
    const lines = source.split("\n")
    const offsets: number[] = []
    let acc = 0
    for (const line of lines) {
      offsets.push(acc)
      acc += line.length + 1
    }
    const code = blankComments(source)
    const codeLines = code.split("\n")
    const starts: number[] = []
    for (let n = 0; n < codeLines.length; n++) {
      if (TOP_LEVEL.test(codeLines[n])) starts.push(n)
    }
    const out: Declaration[] = []
    for (let k = 0; k < starts.length; k++) {
      const n = starts[k]
      const m = /^(?:(?:@\[[^\]]*\]\s*)|(?:noncomputable|private|protected|partial|nonrec)\s+)*(theorem|lemma|def|abbrev|instance)\s+([^\s:({[⦃]+)/.exec(
        codeLines[n],
      )
      if (!m) continue
      const start = offsets[n]
      const end = k + 1 < starts.length ? offsets[starts[k + 1]] : source.length
      const nameEnd = start + m.index + m[0].length
      const assign = findAssign(code, nameEnd, end)
      out.push({
        name: m[2],
        keyword: m[1],
        start,
        end,
        assign,
        signature: source.slice(nameEnd, assign ?? end).trim(),
      })
    }
    return out
  }

  /** Find a declaration by short or qualified name (matching the last components). */
  export function findDeclaration(source: string, name: string) {
    const decls = declarations(source)
    return (
      decls.find((d) => d.name === name) ??
      decls.find((d) => name.endsWith("." + d.name) || d.name.endsWith("." + name))
    )
  }

  /** Replace comment characters by spaces (offsets and line structure preserved). */
  export function blankComments(text: string) {
    const chars = text.split("")
    let i = 0
    let depth = 0
    while (i < text.length) {
      if (text.startsWith("/-", i)) {
        depth++
        chars[i] = chars[i + 1] = " "
        i += 2
        continue
      }
      if (depth && text.startsWith("-/", i)) {
        depth--
        chars[i] = chars[i + 1] = " "
        i += 2
        continue
      }
      if (depth) {
        if (chars[i] !== "\n") chars[i] = " "
        i++
        continue
      }
      if (text.startsWith("--", i)) {
        while (i < text.length && text[i] !== "\n") chars[i++] = " "
        continue
      }
      if (text[i] === '"') {
        // skip string literals so `:=` or `--` inside them is ignored
        i++
        while (i < text.length && text[i] !== '"') i += text[i] === "\\" ? 2 : 1
        i++
        continue
      }
      i++
    }
    return chars.join("")
  }

  function findAssign(code: string, from: number, to: number) {
    let depth = 0
    for (let i = from; i < to - 1; i++) {
      const c = code[i]
      if (c === "(" || c === "[" || c === "{" || c === "⦃" || c === "⟨") depth++
      else if (c === ")" || c === "]" || c === "}" || c === "⦄" || c === "⟩") depth--
      else if (depth === 0 && c === ":" && code[i + 1] === "=") return i
    }
    return undefined
  }

  /** Package module roots that may be imported by a solution (KNOWN_PROBLEMS K1). */
  export function importRoots() {
    return (process.env.OPENCODE_LEAN_GATE_IMPORT_ROOTS ?? "Prosa,Mathlib,CaseStudies")
      .split(",")
      .map((item) => item.trim())
      .filter(Boolean)
  }

  /**
   * `{α} (x : α) : P x` → `∀ {α} (x : α), P x` (the type of a declaration from its binders and result type).
   * Returns undefined when the signature has no binders (then it is `: T` and the type is `T`).
   */
  export function binderSignatureAsType(signature: string) {
    const code = blankComments(signature)
    let depth = 0
    for (let i = 0; i < code.length; i++) {
      const c = code[i]
      if ("([{⦃⟨".includes(c)) depth++
      else if (")]}⦄⟩".includes(c)) depth--
      else if (depth === 0 && c === ":" && code[i + 1] !== "=") {
        const binders = signature.slice(0, i).trim()
        const type = signature.slice(i + 1).trim()
        return binders ? `∀ ${binders}, ${type}` : type
      }
    }
    return undefined
  }
}
