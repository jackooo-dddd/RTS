// [replicate-prosa-buddy patch 11b] Formatting-insensitive comparison of proof-plan normal forms.
//
// The materialization review compared a delegated region's `normal_form` contract with the accepted
// plan's text after only whitespace/case normalization. In 2005-ECRTS-Lemma3 run 20261007_143032 the
// two texts were the same statement but differed in (a) doubled backslashes (`\\sum` instead of
// `\sum`, a JSON double-escaping slip in the model's edit that survived only inside the contract
// comment, where the compiler never sees it) and (b) redundant outer parentheses. The review stayed
// "drifted" for 39 checkpoints, its message did not say what differed, and no lemma was dispatched.
//
// `cosmetic` removes only such presentation differences; `describeDifference` reports the first
// remaining difference so the prover can repair the right text.

export namespace NormalFormText {
  // Same algorithm as eraseBinderTypes in tool/coq-session.ts (patch 5); copied because coq-session
  // imports proof-workflow, so importing it here would create a cycle.
  // `forall x : T,` / `forall (x y : T) (z : U),` become `forall x y z,` (same for exists/fun).
  export function eraseBinderTypes(text: string): string {
    let out = ""
    let index = 0
    const keyword = /\b(forall|exists|fun)\s+/g
    while (true) {
      keyword.lastIndex = index
      const match = keyword.exec(text)
      if (!match) return out + text.slice(index)
      out += text.slice(index, match.index) + match[1] + " "
      const cursor = match.index + match[0].length
      const terminator = match[1] === "fun" ? "=>" : ","
      let depth = 0
      let end = -1
      for (let i = cursor; i < text.length; i++) {
        const char = text[i]
        if (char === "(" || char === "[" || char === "{") depth += 1
        else if (char === ")" || char === "]" || char === "}") depth -= 1
        else if (depth === 0 && text.startsWith(terminator, i)) {
          end = i
          break
        }
      }
      if (end < 0) return out + text.slice(cursor)
      const binders = text.slice(cursor, end).trim()
      const groups = binders.startsWith("(")
        ? [...binders.matchAll(/\(([^()]*)\)/g)].map((group) => group[1])
        : [binders]
      const names = groups.map((group) => {
        const colon = group.indexOf(":")
        return (colon >= 0 ? group.slice(0, colon) : group).trim()
      })
      out += names.filter(Boolean).join(" ") + (terminator === "," ? "," : " =>")
      index = end + terminator.length
    }
  }

  // Collapse doubled backslashes, erase binder types, then ignore parentheses, spacing, case and a
  // final period.
  export function cosmetic(text: string | undefined): string {
    return eraseBinderTypes((text ?? "").replace(/\\{2,}/g, "\\"))
      .replace(/[()]/g, " ")
      .replace(/\s+/g, " ")
      .replace(/\s+([,.])/g, "$1")
      .trim()
      .replace(/\.$/, "")
      .toLowerCase()
  }

  export function sameModuloFormatting(a: string | undefined, b: string | undefined): boolean {
    const left = cosmetic(a)
    return left.length > 0 && left === cosmetic(b)
  }

  // [replicate-prosa-buddy patch 15] Statement comparison for the materialization review. Unlike
  // `cosmetic` (still used for live-goal matching, where Rocq drops parentheses when printing), it keeps
  // every parenthesis that can change grouping: `a - (b - c)` and `a - b - c` stay different. It removes
  // only redundant parentheses (around a single atom, or around the whole text), and it renames bound
  // variables canonically, so `forall k rub_k, k < n` equals `forall k0 rub0, k0 < n` (Rocq renames a
  // binder to `k0` when `k` is already in context; 2015-book-Theorem18_6 run 20261008_182127).
  const word = (name: string) => new RegExp(`(?<![\\w'])${name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![\\w'])`, "g")

  function renameBound(text: string, start: number, names: string[], counter: { n: number }): string {
    let rest = text.slice(start)
    for (const name of names) {
      if (!/^[A-Za-z_][\w']*$/.test(name)) continue
      rest = rest.replace(word(name), `_b${counter.n++}`)
    }
    return text.slice(0, start) + rest
  }

  function canonicalBinders(text: string): string {
    const counter = { n: 0 }
    let out = text
    // forall/exists/fun binders (types already erased: `forall x y,` / `fun x =>`).
    const quantifier = /\b(forall|exists|fun)\s+([\w' ]+?)\s*(,|=>)/g
    for (let index = 0; ; ) {
      quantifier.lastIndex = index
      const match = quantifier.exec(out)
      if (!match) break
      const names = match[2].trim().split(/\s+/).filter(Boolean)
      out = renameBound(out, match.index + match[1].length, names, counter)
      index = match.index + 1
    }
    // MathComp big operators: `\sum_(x <- s)`, `\sum_((x, y) <- s)`, `\max_(i < n | P i)`, `\big[op/idx]_(x in A)`.
    const bigop = /\\(?:sum|prod|max|min|big\[[^\]]*\])_\(\s*(\(\s*[\w']+\s*(?:,\s*[\w']+\s*)*\)|[\w']+)\s*(?:<-|<|in\b|\|)/g
    for (let index = 0; ; ) {
      bigop.lastIndex = index
      const match = bigop.exec(out)
      if (!match) break
      const names = match[1].replace(/[()]/g, " ").split(/[\s,]+/).filter(Boolean)
      out = renameBound(out, match.index, names, counter)
      index = match.index + 1
    }
    return out
  }

  function matchingOuterParens(text: string): boolean {
    if (!text.startsWith("(") || !text.endsWith(")")) return false
    let depth = 0
    for (let i = 0; i < text.length; i++) {
      if (text[i] === "(") depth += 1
      else if (text[i] === ")") depth -= 1
      if (depth === 0 && i < text.length - 1) return false
    }
    return depth === 0
  }

  // In compact text (no spaces around symbols): the relational operator (level 70) starting at `i`, if any.
  function relationAt(s: string, i: number): string | undefined {
    for (const op of ["<=", ">=", "<>", "==", "!="]) if (s.startsWith(op, i)) return op
    if (s.startsWith("<->", i) || s.startsWith("<-", i) || s.startsWith("=>", i)) return undefined
    if (s[i] === "<" || s[i] === ">" || s[i] === "=") return s[i]
    return undefined
  }

  function relationEndsAt(s: string, end: number): boolean {
    const before = s.slice(0, end)
    if (before.endsWith("->") || before.endsWith("<-") || before.endsWith("=>")) return false
    return /(<=|>=|<>|==|!=|<|>|=)$/.test(before)
  }

  // A parenthesized group can be dropped when it is a whole side of a relation (`(F) <= x`, `x = (F)`) and
  // nothing at its top level binds more loosely than a relation (implications, connectives, commas, casts,
  // binders, if/match/let). `a - (b - c)` keeps its parentheses because the group is not a relation operand.
  function looseTopLevel(inner: string): boolean {
    let depth = 0
    for (let i = 0; i < inner.length; i++) {
      const c = inner[i]
      if ("([{".includes(c)) depth += 1
      else if (")]}".includes(c)) depth -= 1
      else if (depth === 0) {
        if (/^(->|\/\\|\\\/|=>|,|:)/.test(inner.slice(i)) || relationAt(inner, i)) return true
        if (/^(if|match|fun|forall|exists|let)(?![\w'])/.test(inner.slice(i)) && (i === 0 || !/[\w']/.test(inner[i - 1])))
          return true
      }
    }
    return false
  }

  function dropRelationOperandParens(s: string): string {
    for (let i = 0; i < s.length; i++) {
      if (s[i] !== "(") continue
      let depth = 0
      let j = i
      for (; j < s.length; j++) {
        if (s[j] === "(") depth += 1
        else if (s[j] === ")" && --depth === 0) break
      }
      if (j >= s.length) return s
      const inner = s.slice(i + 1, j)
      const before = s.slice(0, i)
      const after = s.slice(j + 1)
      const leftOperand = (before === "" || /(->|\/\\|\\\/|\(|,)$/.test(before)) && relationAt(s, j + 1) !== undefined
      const rightOperand = relationEndsAt(s, i) && (after === "" || /^(->|\/\\|\\\/|\)|,)/.test(after))
      if ((leftOperand || rightOperand) && !looseTopLevel(inner)) return dropRelationOperandParens(before + inner + after)
    }
    return s
  }

  export function statement(text: string | undefined): string {
    let out = canonicalBinders(eraseBinderTypes((text ?? "").replace(/\\{2,}/g, "\\")))
      .replace(/\s+/g, " ")
      .trim()
      .replace(/\s*\.$/, "")
    for (let previous = ""; previous !== out; ) {
      previous = out
      out = out.replace(/\(\s*([\w'.]+)\s*\)/g, " $1 ").replace(/\s+/g, " ").trim()
      if (matchingOuterParens(out)) out = out.slice(1, -1).trim()
    }
    return dropRelationOperandParens(out.replace(/\s*([^\w\s'])\s*/g, "$1")).toLowerCase()
  }

  // The statement left after `intros`: strip one leading `forall xs,` or one top-level premise `P ->`.
  // Bound names stay as written, so the stripped variables become free and match a region that states
  // the conclusion with them already in context.
  function introducedOnce(text: string): string | undefined {
    const trimmed = eraseBinderTypes(text.replace(/\\{2,}/g, "\\")).trim()
    const binder = /^forall\s+[\w' ]+?\s*,/.exec(trimmed)
    if (binder) return trimmed.slice(binder[0].length).trim()
    let depth = 0
    for (let i = 0; i < trimmed.length - 1; i++) {
      const c = trimmed[i]
      if ("([{".includes(c)) depth += 1
      else if (")]}".includes(c)) depth -= 1
      else if (depth === 0 && trimmed.startsWith("->", i) && trimmed[i - 1] !== "<") return trimmed.slice(i + 2).trim()
      else if (depth === 0 && /^(forall|exists|fun)(?![\w'])/.test(trimmed.slice(i)) && (i === 0 || !/[\w']/.test(trimmed[i - 1])))
        return undefined
    }
    return undefined
  }

  function sameAfterIntros(closed: string, open: string): boolean {
    const target = statement(open)
    for (let current: string | undefined = closed, steps = 0; current && steps < 32; steps++) {
      current = introducedOnce(current)
      if (current && statement(current) === target) return true
    }
    return false
  }

  export function sameStatement(a: string | undefined, b: string | undefined): boolean {
    const left = statement(a)
    if (left.length === 0) return false
    if (left === statement(b)) return true
    // [replicate-prosa-buddy patch 15] A region may state the conclusion with the plan's leading binders
    // and premises already introduced (2009-RTSS-Lemma3 run 20261008_214657 `clipped_sum_bound`).
    return sameAfterIntros(a ?? "", b ?? "") || sameAfterIntros(b ?? "", a ?? "")
  }

  // [replicate-prosa-buddy patch 15] A plan normal_form written in English ("for each admissible t and pair
  // in hp_bounds, ...", 2009-RTSS-Lemma3 run 20261008_214657; "response time of j > R", 2015-RTAS-Lemma8) can
  // never equal a Coq region statement, so the review falls back to the region's own target-shape check
  // for such nodes. Detected by one strong English word that never occurs in a Coq statement, or two weaker ones.
  export function looksLikeProse(text: string | undefined): boolean {
    const source = text ?? ""
    if (/(?<![\\\w'])(the|of|each|every|over|whose|where|admissible|relevant)(?![\w'])/i.test(source)) return true
    const words = source.match(/(?<![\\\w'])(is|are|such|that|which|selected|same|any|when|its)(?![\w'])/gi)
    return new Set((words ?? []).map((word) => word.toLowerCase())).size >= 2
  }

  // [replicate-prosa-buddy patch 15] Only the first line of a multi-line `normal_form:` marker value is
  // parsed, so a region contract can arrive cut off ("forall x : sporadic_task -> time,", 2015-RTAS-Lemma8
  // `capped_sum`/`excess_task`). Such a fragment can never equal the plan; the review falls back to the
  // target-shape check for it, as for prose.
  export function looksTruncated(text: string | undefined): boolean {
    const trimmed = (text ?? "").trim()
    if (!trimmed) return false
    if (/(,|->|<->|\/\\|\\\/|=>|:)$/.test(trimmed)) return true
    let depth = 0
    for (const c of trimmed) {
      if (c === "(") depth += 1
      else if (c === ")") depth -= 1
    }
    return depth !== 0
  }

  // Human-readable first difference after `statement` normalization, for checkpoint blockers.
  export function describeDifference(plan: string | undefined, region: string | undefined, context = 45): string {
    const a = statement(plan)
    const b = statement(region)
    if (!b) return "the region has no normal_form contract; copy the accepted plan normal_form into it"
    let i = 0
    while (i < a.length && i < b.length && a[i] === b[i]) i++
    const from = Math.max(0, i - 15)
    const snippet = (text: string) =>
      (from > 0 ? "…" : "") + text.slice(from, i + context) + (i + context < text.length ? "…" : "")
    return (
      `first difference (ignoring spacing, redundant parentheses, doubled backslashes, binder types and ` +
      `bound-variable names, shown normalized with bound variables as _b0, _b1, ...): ` +
      `plan "${snippet(a)}" vs region "${snippet(b)}". ` +
      "Copy the accepted plan normal_form verbatim into the region's normal_form contract and have statement, " +
      "or submit an authorized plan repair if the target must change."
    )
  }
}
