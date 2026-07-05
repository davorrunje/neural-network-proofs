---
name: formalizing-papers-in-lean
description: Use when translating a research paper's results into machine-checked Lean 4 + Mathlib theorems, or when starting any paper-to-Lean formalization in an existing Lean project.
---

# Formalizing Papers in Lean

## Overview

Turning a paper into trustworthy Lean is an **orchestration** problem, not a coding sprint: scope
what to state faithfully, plan the decomposition, execute with review, and verify the axiom profile —
not just a green build. This skill wires the general process skills to the Lean domain and collects
the Lean-specific facts that are easy to miss.

Core principle: **a green `lake build` does NOT mean the theorem is proved.** `sorry` is only a
warning; the proof is trustworthy only when its *axiom profile* is clean. Verify that explicitly.

## When to Use

- Translating a paper's theorem(s) into Lean 4 + Mathlib.
- Any "formalize X so it's machine-checked" task in a Lean repo.
- Not for: editing an existing Lean development's style (use `auditing-lean-proofs` /
  `polishing-lean-proofs`), or non-Lean formalization.

## Workflow (orchestrate — do not hand-code end to end)

1. **Scope + faithful statements — REQUIRED SUB-SKILL: use superpowers:brainstorming.** Decide
   *which* results to formalize, write each target theorem's Lean statement faithful to the paper
   (no silently added hypotheses, no weakened conclusion), name the **headline theorem(s)**, and list
   what is out of scope. The headline names + statements become the *frozen* contract every later
   step (and any future `polishing-lean-proofs` pass) must preserve.
2. **Plan — REQUIRED SUB-SKILL: use superpowers:writing-plans.** Decompose into files/lemmas in
   dependency order; state the per-task verification and the frozen headlines as Global Constraints.
3. **Execute — REQUIRED SUB-SKILL: use superpowers:subagent-driven-development.** One implementer +
   reviewer per file; controller commits and runs the axiom gate. Prove leaves bottom-up.
4. **Verify** every headline with the Axiom Gate below before claiming done.

## Faithfulness (the one rule that is Lean-specific here)

State the paper's theorem, then read the Lean statement next to the paper's and confirm every
hypothesis and the conclusion match. A convenient-but-different statement is a silent failure.
When the paper's proof has a gap or a step Mathlib can't yet support, **report it (NEEDS_CONTEXT) —
never `sorry` it and never strengthen the hypotheses to dodge it** (this repo's `CLAUDE.md` also
mandates this).

## Axiom Gate (the verification agents most often get wrong)

A `sorry` produces only a *warning*, so `lake build` can be green over an unproved theorem.
The real gate, per headline, on **freshly built** oleans:

```bash
lake build                       # MUST rebuild first — see stale-olean gotcha
lake env lean -c 'import <Root>
#print axioms <Namespace>.<headline>'   # or a small check file
```

Expect exactly `[propext, Classical.choice, Quot.sound]`. Any `sorryAx` = unproved; any other axiom
= an unintended assumption. If the repo has a `scripts/check_sorry_free.lean` (or equivalent) gate,
**add every new headline to it** as you formalize, so CI checks the axiom profile of each one.

## Lean gotchas reference

| Gotcha | What to do |
|---|---|
| `sorry` is a warning, not an error | Never trust a green build alone — run the Axiom Gate. |
| `#print axioms` reads the compiled `.olean`, not source | After edits/moves/renames, `lake build` **before** trusting `#print axioms` (stale olean reports old axioms). |
| Default target must transitively import a theorem or `lake build` won't check it | Re-export headlines from the root module. |
| Many `import Mathlib` modules building at once → `Too many open files` (EMFILE); this Lake has no `-j` | After a mass invalidation, build serially one module at a time in dependency order (Mathlib stays cached). |
| `import Mathlib` (whole-library) makes `lake build` slow and worsens EMFILE | Not Mathlib-idiomatic — the standard is minimal precise imports. Prefer targeted imports where practical (`lake exe shake` / `#min_imports`, confirmed by a build); a repo may keep blanket imports for internal code by explicit, documented decision. |
| Line length | ≤ 100 **codepoints** (Mathlib glyphs are 1 cp; byte tools over-report — measure codepoints). |
| SSH-signed commits + no-force-push branch rules | If signing needs live confirmation and you're unattended, commit unsigned and batch-sign **only the unpushed** commits before the PR (`git rebase --exec 'git commit --amend --no-edit -S' <last-pushed>`) — never re-sign already-pushed commits. |

## Common Mistakes

- Claiming "done / machine-checked" on a green build without the Axiom Gate.
- Running `#print axioms` against a stale olean (no rebuild after edits) and trusting the result.
- Hand-coding the whole formalization solo instead of orchestrating (scope → plan → per-file review).
- Letting the Lean statement drift from the paper's; not cross-checking; silently adding hypotheses.
