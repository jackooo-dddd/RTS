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

  // Human-readable first difference after `cosmetic` normalization, for checkpoint blockers.
  export function describeDifference(plan: string | undefined, region: string | undefined, context = 45): string {
    const a = cosmetic(plan)
    const b = cosmetic(region)
    if (!b) return "the region has no normal_form contract; copy the accepted plan normal_form into it"
    let i = 0
    while (i < a.length && i < b.length && a[i] === b[i]) i++
    const from = Math.max(0, i - 15)
    const snippet = (text: string) =>
      (from > 0 ? "…" : "") + text.slice(from, i + context) + (i + context < text.length ? "…" : "")
    return (
      `first difference (ignoring spacing, parentheses, doubled backslashes and binder types): ` +
      `plan "${snippet(a)}" vs region "${snippet(b)}". ` +
      "Copy the accepted plan normal_form verbatim into the region's normal_form contract and have statement, " +
      "or submit an authorized plan repair if the target must change."
    )
  }
}
