/**
 * Delegated proof regions in Lean source (prompt_revision.md §0.1, DECISIONS R1, D10).
 *
 * A region is delimited by comment markers and contains exactly one exported target with an outer parenthesised
 * proof wrapper:
 *
 *     /- proof_region begin owner: lemma admit_id: A1 theorem: solution target: hA plan_node: n1 -/
 *     have hA : P := (by
 *       …
 *     )
 *     /- proof_region end admit_id: A1 -/
 *
 * Line-comment markers (`-- proof_region begin …`, `-- proof_region end …`) are accepted too. The parser does genuine
 * delimiter matching (nested brackets, string/char literals, line and nested block comments); a missing wrapper,
 * unbalanced parentheses or ambiguous bounds are structural errors, never guesses.
 */
export namespace LeanRegion {
  export type Region = {
    admit_id: string
    /** Marker attributes (`key: value`, values run to the next known key). */
    attributes: Record<string, string>
    beginStart: number
    beginEnd: number
    endStart: number
    endEnd: number
    target?: {
      name: string
      /** The proposition text between `have <name> :` and `:=`. */
      statement: string
      haveStart: number
      /** Offset of the outer `(` of `:= (by …)`. */
      open: number
      /** Offset of the matching `)`. */
      close: number
      /** Offset just after `by` (start of the tactic block). */
      byEnd: number
    }
  }

  export type ParseResult = { regions: Region[]; errors: { admit_id?: string; offset: number; message: string }[] }

  /** Known marker field names; only these start a new `key: value`. */
  export const MARKER_FIELDS = ["owner", "admit_id", "theorem", "target", "plan_node", "kind", "layer"]

  const BEGIN = /(?:\/-\s*proof_region\s+begin\b([\s\S]*?)-\/|--[ \t]*proof_region[ \t]+begin\b([^\n]*))/g
  const END = /(?:\/-\s*proof_region\s+end\b([\s\S]*?)-\/|--[ \t]*proof_region[ \t]+end\b([^\n]*))/g

  /** Parse `key: value` attributes; a value runs to the next known field name (bracket- and quote-aware). */
  export function attributes(text: string, fields = MARKER_FIELDS) {
    const out: Record<string, string> = {}
    const starts: { key: string; at: number; valueAt: number }[] = []
    let depth = 0
    let quote = false
    for (let i = 0; i < text.length; i++) {
      const c = text[i]
      if (c === '"') quote = !quote
      if (quote) continue
      if ("([{⟨⦃".includes(c)) depth++
      else if (")]}⟩⦄".includes(c)) depth = Math.max(0, depth - 1)
      if (depth || (i > 0 && !/[\s;,]/.test(text[i - 1]))) continue
      for (const key of fields) {
        if (text.startsWith(key, i) && /^\s*:/.test(text.slice(i + key.length))) {
          const colon = text.indexOf(":", i + key.length)
          starts.push({ key, at: i, valueAt: colon + 1 })
          break
        }
      }
    }
    for (let k = 0; k < starts.length; k++) {
      const end = k + 1 < starts.length ? starts[k + 1].at : text.length
      out[starts[k].key] = text.slice(starts[k].valueAt, end).trim().replace(/[;,]$/, "").trim()
    }
    return out
  }

  /** Character classes that do not count for delimiter matching: comments, strings and char literals. */
  export function codeMask(source: string) {
    const code = new Array<boolean>(source.length).fill(true)
    let i = 0
    while (i < source.length) {
      if (source.startsWith("--", i)) {
        while (i < source.length && source[i] !== "\n") code[i++] = false
        continue
      }
      if (source.startsWith("/-", i)) {
        let depth = 0
        while (i < source.length) {
          if (source.startsWith("/-", i)) {
            depth++
            code[i] = code[i + 1] = false
            i += 2
          } else if (source.startsWith("-/", i)) {
            depth--
            code[i] = code[i + 1] = false
            i += 2
            if (!depth) break
          } else code[i++] = false
        }
        continue
      }
      if (source[i] === '"') {
        code[i++] = false
        while (i < source.length && source[i] !== '"') {
          if (source[i] === "\\") code[i++] = false
          code[i++] = false
        }
        if (i < source.length) code[i++] = false
        continue
      }
      // char literal 'x' or '\n' (but not a prime in an identifier such as `h'`)
      if (source[i] === "'" && (i === 0 || !/[\p{L}\p{N}_'!?]/u.test(source[i - 1]))) {
        const close = source[i + 1] === "\\" ? i + 3 : i + 2
        if (source[close] === "'") {
          for (let j = i; j <= close; j++) code[j] = false
          i = close + 1
          continue
        }
      }
      i++
    }
    return code
  }

  /** Offset of the bracket matching the opening one at `open` (code characters only), or undefined. */
  export function matchBracket(source: string, open: number, mask = codeMask(source)) {
    const pairs: Record<string, string> = { "(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄" }
    const stack: string[] = []
    for (let i = open; i < source.length; i++) {
      if (!mask[i]) continue
      const c = source[i]
      if (pairs[c]) stack.push(pairs[c])
      else if (")]}⟩⦄".includes(c)) {
        if (stack.pop() !== c) return undefined
        if (!stack.length) return i
      }
    }
    return undefined
  }

  export function parse(source: string): ParseResult {
    const mask = codeMask(source)
    const regions: Region[] = []
    const errors: ParseResult["errors"] = []
    const ends: { start: number; end: number; admit_id?: string }[] = []
    END.lastIndex = 0
    for (let m: RegExpExecArray | null; (m = END.exec(source)); ) {
      const attrs = attributes(m[1] ?? m[2] ?? "")
      ends.push({ start: m.index, end: m.index + m[0].length, admit_id: attrs.admit_id || undefined })
    }
    BEGIN.lastIndex = 0
    for (let m: RegExpExecArray | null; (m = BEGIN.exec(source)); ) {
      const attrs = attributes(m[1] ?? m[2] ?? "")
      const admit = attrs.admit_id
      const beginStart = m.index
      const beginEnd = m.index + m[0].length
      if (!admit) {
        errors.push({ offset: beginStart, message: "proof_region begin marker without admit_id" })
        continue
      }
      const end = ends.find((e) => e.start > beginEnd && (!e.admit_id || e.admit_id === admit))
      if (!end) {
        errors.push({ admit_id: admit, offset: beginStart, message: `proof_region ${admit} has no end marker` })
        continue
      }
      const nested = [...source.slice(beginEnd, end.start).matchAll(BEGIN)]
      BEGIN.lastIndex = beginEnd
      if (nested.length) {
        errors.push({ admit_id: admit, offset: beginStart, message: `proof_region ${admit} contains another begin marker before its end marker` })
        continue
      }
      const region: Region = { admit_id: admit, attributes: attrs, beginStart, beginEnd, endStart: end.start, endEnd: end.end }
      const target = findTarget(source, beginEnd, end.start, attrs.target, mask)
      if (typeof target === "string") errors.push({ admit_id: admit, offset: beginStart, message: target })
      else region.target = target
      regions.push(region)
    }
    return { regions, errors }
  }

  /** The exported `have <name> : P := (by …)` inside a region: the last `have` (helpers may precede it). */
  function findTarget(source: string, from: number, to: number, wanted: string | undefined, mask: boolean[]): Region["target"] | string {
    const haves: number[] = []
    const re = /\bhave\s+/g
    re.lastIndex = from
    for (let m: RegExpExecArray | null; (m = re.exec(source)) && m.index < to; ) if (mask[m.index]) haves.push(m.index)
    const candidates: NonNullable<Region["target"]>[] = []
    for (const at of haves) {
      const head = /^have\s+([^\s:(]+)\s*:/.exec(source.slice(at))
      if (!head) continue
      const name = head[1]
      // the statement runs to the first `:=` at depth 0 (code only)
      let depth = 0
      let assign: number | undefined
      for (let i = at + head[0].length; i < to - 1; i++) {
        if (!mask[i]) continue
        const c = source[i]
        if ("([{⟨⦃".includes(c)) depth++
        else if (")]}⟩⦄".includes(c)) depth--
        else if (depth === 0 && c === ":" && source[i + 1] === "=") {
          assign = i
          break
        }
      }
      if (assign === undefined) continue
      const after = /^:=\s*\(\s*by\b/.exec(source.slice(assign))
      if (!after) continue
      const open = source.indexOf("(", assign)
      const close = matchBracket(source, open, mask)
      if (close === undefined || close > to) return `the proof wrapper of ${name} has unbalanced parentheses or ends after the region's end marker`
      candidates.push({
        name,
        statement: source.slice(at + head[0].length, assign).trim(),
        haveStart: at,
        open,
        close,
        byEnd: assign + after[0].length,
      })
    }
    if (!candidates.length) return "no `have <name> : <statement> := (by …)` target inside the region"
    if (wanted) {
      const named = candidates.filter((c) => c.name === wanted)
      if (named.length === 1) return named[0]
      if (named.length > 1) return `target ${wanted} is declared more than once in the region`
    }
    // the exported target is the outermost wrapper that is not nested inside another candidate
    const outer = candidates.filter((c) => !candidates.some((o) => o !== c && o.open < c.open && c.close < o.close))
    if (outer.length !== 1) return "ambiguous region: several top-level `have … := (by …)` targets and no `target:` attribute"
    return outer[0]
  }

  /**
   * Replace the tactic block of the given regions by `sorry` (the wrapper becomes `(by sorry)`). Regions are rewritten
   * from the end so offsets stay valid. Returns the new text.
   */
  export function maskRegions(source: string, regions: Region[]) {
    let out = source
    for (const region of [...regions].filter((r) => r.target).sort((a, b) => b.target!.open - a.target!.open)) {
      const t = region.target!
      out = out.slice(0, t.byEnd) + " sorry" + out.slice(t.close)
    }
    return out
  }
}
