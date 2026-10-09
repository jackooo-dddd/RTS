/**
 * Safety checks for Lean *terms* that the tools elaborate on the agent's behalf (statement equivalence, root goals,
 * `normal_form`, `inspect` expressions) — known-problem-fixes/lean_session-equivalence.md.
 *
 * `show b` unifies, so a `b` containing a term hole (`_`, `?x`, `?_`) or `sorry` matches almost any goal. Statements
 * are therefore scanned token by token (never as substrings) before any check:
 * - identifiers follow Lean's rules (letters/`_` first; then letters, digits, `_`, `'`, `!`, `?`, subscripts;
 *   `.`-separated parts; `«…»` quoting), so underscores inside names (`job_cost`) and a trailing `?`/`!`
 *   (`List.get?`) are ordinary;
 * - a standalone `_` is allowed only as a binder name (`fun _ =>`, `∀ _,`, `∃ _,`, `(_ : T)`);
 * - `?x`, `?_` and the identifiers `sorry`/`sorryAx` are rejected;
 * - a universe metavariable `?u.N` after `Sort`/`Type` or inside `.{…}` is replaced by the level hole `_`
 *   (pretty-printed goals occasionally show unsolved levels; a level hole cannot absorb a subterm).
 */
export namespace LeanTerm {
  export type Scan = { ok: true; text: string } | { ok: false; token: string; offset: number; reason: string }

  const ID_START = /[\p{L}_]/u
  const ID_REST = /[\p{L}\p{N}_'!?₀-ₜᵢ-ᵪ]/u

  type Token = { kind: "ident" | "hole" | "mvar" | "other" | "space"; text: string; offset: number }

  function tokenize(text: string): Token[] {
    const out: Token[] = []
    let i = 0
    while (i < text.length) {
      const c = text[i]
      if (/\s/.test(c)) {
        let j = i
        while (j < text.length && /\s/.test(text[j])) j++
        out.push({ kind: "space", text: text.slice(i, j), offset: i })
        i = j
        continue
      }
      if (c === "«") {
        const j = text.indexOf("»", i)
        const end = j < 0 ? text.length : j + 1
        out.push({ kind: "ident", text: text.slice(i, end), offset: i })
        i = end
        continue
      }
      if (c === "?" && i + 1 < text.length && (ID_START.test(text[i + 1]) || text[i + 1] === "_")) {
        let j = i + 1
        while (j < text.length && (ID_REST.test(text[j]) || (text[j] === "." && j + 1 < text.length && /[\p{L}\p{N}_]/u.test(text[j + 1])))) j++
        out.push({ kind: "mvar", text: text.slice(i, j), offset: i })
        i = j
        continue
      }
      if (ID_START.test(c)) {
        let j = i + 1
        while (j < text.length) {
          if (ID_REST.test(text[j])) j++
          else if (text[j] === "." && j + 1 < text.length && (ID_START.test(text[j + 1]) || text[j + 1] === "«")) j++
          else break
        }
        const word = text.slice(i, j)
        out.push({ kind: word === "_" ? "hole" : "ident", text: word, offset: i })
        i = j
        continue
      }
      out.push({ kind: "other", text: c, offset: i })
      i++
    }
    return out
  }

  /** Previous / next non-space token. */
  function neighbour(tokens: Token[], index: number, step: -1 | 1) {
    for (let k = index + step; k >= 0 && k < tokens.length; k += step) if (tokens[k].kind !== "space") return tokens[k]
    return undefined
  }

  function isBinderHole(tokens: Token[], index: number) {
    const prev = neighbour(tokens, index, -1)
    const next = neighbour(tokens, index, 1)
    // fun _ =>, fun _ _ =>, λ _ ↦
    if (prev && ["fun", "λ"].includes(prev.text)) return true
    // ∀ _, ∃ _, ∀ _ _,
    if (prev && ["∀", "∃", "Π", "Σ", "∃!", "forall", "exists"].includes(prev.text)) return true
    // (_ : T), {_ : T}, ⦃_ : T⦄, [_ : C]
    if (prev && ["(", "{", "⦃", "["].includes(prev.text) && next?.text === ":") return true
    // a run of binder names: ∀ x _ y, / fun x _ =>
    if (prev?.kind === "ident" || prev?.kind === "hole") {
      for (let k = index - 1; k >= 0; k--) {
        const t = tokens[k]
        if (t.kind === "space" || t.kind === "ident" || t.kind === "hole") {
          if (["fun", "λ", "∀", "∃", "forall", "exists"].includes(t.text)) return true
          continue
        }
        break
      }
    }
    return false
  }

  function inUniversePosition(tokens: Token[], index: number) {
    const prev = neighbour(tokens, index, -1)
    if (prev && (prev.text === "Sort" || prev.text === "Type")) return true
    // inside `.{ … }`
    let depth = 0
    for (let k = index - 1; k >= 0; k--) {
      const t = tokens[k]
      if (t.text === "}") depth++
      else if (t.text === "{") {
        if (depth) depth--
        else return k > 0 && tokens[k - 1].text === "."
      }
    }
    return false
  }

  /** Scan a term; on success returns the text with universe `?u.N` replaced by `_`. */
  export function scan(text: string): Scan {
    const tokens = tokenize(text)
    let out = ""
    for (let index = 0; index < tokens.length; index++) {
      const t = tokens[index]
      if (t.kind === "hole") {
        if (inUniversePosition(tokens, index) || isBinderHole(tokens, index)) {
          out += t.text
          continue
        }
        return { ok: false, token: "_", offset: t.offset, reason: "term hole `_` (a placeholder unifies with anything)" }
      }
      if (t.kind === "mvar") {
        if (/^\?u(?:\.\d+)?$/.test(t.text) && inUniversePosition(tokens, index)) {
          out += "_"
          continue
        }
        return { ok: false, token: t.text, offset: t.offset, reason: `metavariable \`${t.text}\` (a placeholder unifies with anything)` }
      }
      if (t.kind === "ident" && (t.text === "sorry" || t.text === "sorryAx")) {
        return { ok: false, token: t.text, offset: t.offset, reason: "`sorry` is not a statement" }
      }
      out += t.text
    }
    return { ok: true, text: out }
  }

  /** A single pure term: no tactic blocks, commands, `#`-commands, or line breaks that end the term early. */
  export function assertPureTerm(label: string, text: string) {
    if (!text.trim()) throw new Error(`${label} is empty`)
    if (/\p{Cc}/u.test(text.replace(/[\n\t]/g, " "))) throw new Error(`${label} contains control characters`)
    const tokens = tokenize(text)
    for (const t of tokens) {
      if (t.kind === "ident" && (t.text === "by" || t.text === "native_decide")) {
        throw new Error(`${label} must be a term, not a tactic block (\`${t.text}\`)`)
      }
      if (t.kind === "other" && t.text === "#") throw new Error(`${label} must not contain \`#\` commands`)
      if (
        t.kind === "ident" &&
        ["theorem", "lemma", "def", "axiom", "instance", "import", "open", "namespace", "end", "set_option", "attribute", "macro", "syntax", "elab", "run_cmd", "initialize"].includes(t.text)
      ) {
        throw new Error(`${label} must be one term, not a command (\`${t.text}\`)`)
      }
    }
    const stack: string[] = []
    const pairs: Record<string, string> = { ")": "(", "]": "[", "}": "{", "⟩": "⟨", "⦄": "⦃" }
    for (const t of tokens) {
      if (t.kind !== "other") continue
      if ("([{⟨⦃".includes(t.text)) stack.push(t.text)
      else if (pairs[t.text] && stack.pop() !== pairs[t.text]) throw new Error(`${label} has unbalanced delimiters`)
    }
    if (stack.length) throw new Error(`${label} has unbalanced delimiters`)
  }
}
