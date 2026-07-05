---
name: auditing-lean-proofs
description: Use when reviewing existing Lean 4 + Mathlib code against community/Mathlib idiom standards, or to produce a findings list before a polishing or refactor pass.
---

# Auditing Lean Proofs for Mathlib Idiom

## Overview

A **read-only** review that produces a *structured, prioritized* findings list of idiom
improvements. Unaided audits are inconsistent run-to-run: they catch the obvious smells but miss the
subtle high-value ones (reinvented Mathlib defs/lemmas, junk-value hacks) and inject **noise**
(flagging "standards" the repo deliberately doesn't follow). This skill fixes *what to hunt* and
*the shape of the output* so the audit is complete and reproducible.

You FIND and DESCRIBE; you do NOT edit. The findings list feeds `polishing-lean-proofs`.

## When to Use

- Assessing a Lean development against Mathlib standards; prepping a polish/refactor pass.
- Not for: writing new proofs, changing behavior, or changing a theorem's *statement*.

## Idiom checklist — hunt ALL of these, per declaration

The subtle ones (1–4) are the ones unaided reviews miss; do not skip them.

1. **Reinvented Mathlib.** A local def/lemma that already exists in Mathlib — e.g. a hand-rolled
   "monotone on a set" that is `MonotoneOn`; a manual telescoping induction that is
   `Finset.sum_range_sub`. Name the existing Mathlib item.
2. **Non-idiomatic tactics.** Manual steps a library lemma/tactic does in one line — name the
   replacement (`gcongr`, `positivity`, `Finset.sum_*`, `dotProduct_le_dotProduct_of_nonneg_*`, …).
3. **Junk-value / partiality hacks.** `Nat` subtraction `i - 1`, `if i = 0 then … else …`,
   off-range `0` stubs. Prefer honest indexing (`Fin.cons`, forward differences `y (i+1) - y i`,
   `match`).
4. **Extractable lemmas.** A general/reusable fact inlined in a proof or buried `private` — extract
   and name it.
5. **Naming.** Descriptive, Mathlib-convention *declaration* names (no `f` / `w` / `thing`); a
   `theorem`/`def` name reflects its statement. (Single-letter *bound variables* like `x`, `n` are
   fine — this is about declaration names.)
6. **Dead code.** Unused `have`s, unused hypotheses/parameters, unused defs.
7. **Line length > 100 codepoints** (measure codepoints — Mathlib glyphs are 1 cp; byte tools
   over-report).
8. **Hygiene.** Missing docstrings on public decls; leftover `set_option maxHeartbeats`; any
   `sorry`/`admit`.
9. **Cross-file ripple.** Which findings, if fixed, change a signature that other files consume.
10. **Imports & build time.** `import Mathlib` pulls in the entire library, making `lake build` slow
    and worsening `Too many open files` (EMFILE) on parallel builds. Mathlib's own standard is
    *minimal, precise* imports — blanket `import Mathlib` is a genuine build-time + idiom cost, not a
    neutral convention. Flag it, and point at `lake exe shake` (unused-import check) / `#min_imports`
    to derive the real set — but note those UNDER-report (open-scoped notation, instances, tactics),
    so any minimization must be confirmed by a build.

## Verify before you assert

For every "use Mathlib's `X` instead" claim, confirm `X` exists and has the shape you think
(`lean_loogle` / `lean_local_search` / `lean_leansearch`). If those tools are unavailable, verify by
finding `X` in the Mathlib source (a definition, or a call-site `rw [X …]` as surrogate evidence).
Never invent lemma names.

## Respect the repo's conventions (avoid false positives)

Read `CLAUDE.md` / neighboring files for the local norm first. Do NOT flag as issues:
- Absence of unit tests / `example`s — Mathlib does not unit-test its lemmas.
- Missing `@[simp]`/attribute tags, unless there is a concrete reason.

On imports (checklist 10): still flag blanket `import Mathlib`, but calibrate severity to the repo's
intent — REQUIRED (blocking) for upstream-facing / `ForMathlib`-style files; if `CLAUDE.md` documents
a *deliberate* decision to keep blanket imports for internal code (often because minimization proved
fragile), record it as an optional/low-severity build-time note rather than a blocking defect. Do not
silently drop it — the build-time cost is real. Default: treat any file NOT under a directory the
repo designates as upstream-facing (e.g. `ForMathlib/`) as internal.

## Output contract (the findings list)

Group by file. For each finding: `file:line` · category (from the checklist; if it spans two, give
the primary and the secondary in parentheses) · one-line description · concrete fix (name the exact
Mathlib lemma/def) · severity (blocking / important / cosmetic). Mark any
finding that would touch a **frozen** headline *statement* as "STATEMENT — out of scope, flag only".
End with a short **prioritized summary** (highest-value idiom fixes first) and a **cross-file ripple**
note (which fixes propagate to other files).

## Common Mistakes

- A flat, unprioritized list; missing the subtle categories (reinvented Mathlib, junk-values).
- Inventing Mathlib lemma names without verifying they exist.
- Flagging repo conventions (blanket imports, no unit tests) as defects — noise.
- Proposing to change a theorem's *statement* — that is not an idiom fix; flag it as out of scope.
