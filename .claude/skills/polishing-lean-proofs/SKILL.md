---
name: polishing-lean-proofs
description: Use when refactoring existing Lean 4 + Mathlib proofs toward community/Mathlib standards, or running a repeated cleanup pass until a development is idiomatically clean.
---

# Polishing Lean Proofs to Mathlib Standards

## Overview

A **behavior-preserving** refactor that applies an idiom-audit findings list and verifies the proofs
still prove exactly what they did. Two things are non-obvious and easy to get wrong:
- A green `lake build` does NOT prove you preserved behavior when you re-model a *definition* a
  theorem uses.
- "Nothing left to do" must be driven by **re-auditing for idiom**, not by compiler warnings —
  idiom smells (reinvented Mathlib, junk-values, non-idiomatic tactics) produce no warning, so a
  warnings-driven loop stops with smells still present.

Behavior-preserving means: the **frozen** headline theorems keep their exact statements and axiom
profile. Everything else may be re-modeled.

## When to Use

- Applying `auditing-lean-proofs` findings; iterating a Mathlib-standards cleanup to convergence.
- Not for: adding new results, or changing what a theorem proves.

## Workflow

1. **Audit — REQUIRED SUB-SKILL: use auditing-lean-proofs.** Produce/refresh the findings list. Fix
   only what it lists — do not invent changes. Findings marked "STATEMENT — out of scope" are frozen.
2. **Fix — REQUIRED SUB-SKILL: use superpowers:subagent-driven-development.** One implementer +
   reviewer per file, in dependency order (a re-modeled definition ripples to its consumers); the
   controller commits and runs the behavior-preservation gate.
3. **Behavior-preservation gate** (below) after each file and at the end.
4. **Loop to convergence** via the DONE predicate (below), e.g. under `/loop`.

## Behavior-preservation gate (what a green build misses)

Re-modeling a definition `Foo` that a headline `main` references can change what `main` *proves* even
with `main`'s statement text untouched — Lean simply accepts a proof of the new meaning; the build is
green, no warning. `<base>` below = the **fixed** commit the whole polish pass started from
(`git merge-base <target-branch> HEAD` / the pre-polish commit) — NOT `HEAD~1`, which shifts every
iteration. Per frozen headline, the first two checks are ALWAYS required; the third is required
whenever you re-modeled a definition the headline references:

- **Statement byte-identical** (always): `git diff <base> -- <file>` shows no change to the `theorem`
  signature lines.
- **Axiom profile unchanged** (always): `#print axioms main` on **freshly built** oleans = the same
  set (e.g. `[propext, Classical.choice, Quot.sound]`) — no new `sorryAx` or axiom.
- **Meaning re-unifies** (when a referenced def was re-modeled): temporarily add, in the same file,
  `example : <the pre-refactor statement, verbatim> := main`; `lake build` (fresh oleans); if it
  fails to elaborate, the meaning drifted — revert. Delete the `example` before committing. (Also
  `#check @main` before/after to catch implicit/universe shifts.)

## Continuous loop + DONE predicate

Each iteration: **re-run `auditing-lean-proofs`** (a fresh audit of the current tree — not a cached
list) → fix its findings (subagent-driven) → run the gate + build. Drive this with `/loop` (invoke
the polish skill each tick; each tick re-audits). Repeat until ALL of these hold at a single
iteration:

- The **audit produces no new actionable findings** — idiom convergence. *This*, not "no compiler
  warnings" or "no more diffs", is the real stop signal.
- `lake build` green; the sorry-free / axiom gate is clean.
- Every frozen headline passes the behavior-preservation gate.
- All changed files ≤ 100 codepoints; no `set_option maxHeartbeats`, `sorry`, or `admit`.
- A fresh whole-branch review (REQUIRED SUB-SKILL: use superpowers:requesting-code-review) returns no
  Critical/Important findings.

Stopping because an iteration "made no changes" is NOT enough if you never re-audited for idiom —
converge on the audit, not on the diff.

## Common Mistakes

- Trusting a green build after re-modeling a def a headline uses — meaning-drift is silent; run the gate.
- Driving the loop by compiler warnings / "no more diffs" instead of re-auditing — stops with idiom
  smells remaining.
- Changing a theorem's *statement* to make it "cleaner" — out of scope; frozen headlines are frozen.
- Applying changes beyond the audit findings (scope creep).
- Import minimization (cutting `import Mathlib` down to precise imports for build speed / upstream
  readiness) is a legitimate polish target from the audit — but the min-imports tooling under-reports
  (open-scoped notation, instances, tactics), so confirm each reduction by building, and respect a
  documented decision to keep blanket imports for internal code rather than looping on it forever.
