# Resolve Repo Loose Ends Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the documentation, CI, and local-branch loose ends from the whole-repo review, with
no change to any proof, theorem statement, or axiom.

**Architecture:** Three small file edits (CLAUDE.md, the root module docstring, the CI import gate)
land as one `chore:` PR off `main`; stale local branches are pruned separately as a local git
operation (no PR). Everything is docs/CI-config only — the Lean development is untouched.

**Tech Stack:** Lean 4 + Mathlib (Lake), GitHub Actions (`ci.yml`), Markdown docs, git.

## Global Constraints

- No changes to any `.lean` proof, `theorem`/`def`/`lemma` statement, or axiom. Docs + CI-config only.
- Line length ≤ 100 codepoints for Lean source and doc **prose** (Mathlib glyphs count as 1). The
  `CLAUDE.md` layout **table** is exempt: its rows are already >100 by design (Markdown table cells),
  so the added Monotone row may match that length — do not try to wrap table rows.
- Commits are **unsigned** (signing was retired; `commit.gpgsign` is `false` for this repo). Use
  plain `git commit`.
- Branch: `chore/resolve-loose-ends` (already created off `main`; already holds the spec commit
  `a3ca038`). Do not commit to `main` directly.
- After the edits: `lake build NeuralNetworkProofs` is green with zero warnings, and
  `lake env lean scripts/check_sorry_free.lean` reports all 7 headlines as
  `[propext, Classical.choice, Quot.sound]`.
- Spec: `docs/superpowers/specs/2026-07-08-resolve-loose-ends-design.md`.

---

### Task 1: Refresh `CLAUDE.md` for the completed Monotone development

**Files:**
- Modify: `CLAUDE.md` (the "What this is" section ~lines 5–16, the layout table ~lines 22–31)

**Interfaces:** none (documentation).

- [ ] **Step 1: Update "What this is" — three developments, add Monotone, drop "next planned".**
  Replace the current text from `Two developments are complete` through the
  `Next planned work: … monotonic … Monotone/).` paragraph with:

```markdown
`NeuralNetworkProofs` formalizes **universal approximation theorems (UATs) for neural networks** in
Lean 4 + Mathlib. Three developments are complete and `sorry`-free:

- **Cybenko (1989)** — a single-hidden-layer network with a continuous sigmoidal activation is dense
  in `C(K, ℝ)`. Headline: `UniversalApproximation.Cybenko.universal_approximation`.
- **Leshno–Lin–Pinkus–Schocken (1993)** — an `M`-class activation densely approximates iff it is not
  (a.e.) a polynomial. Headline: `UniversalApproximation.Leshno.leshno_dense_iff`.
- **Monotone networks** — depth-4 monotone networks are universal for monotone functions.
  Mikulincer–Reichman (2022): threshold nets interpolate and uniformly approximate
  (`UniversalApproximation.Monotone.monotone_interpolation`, `…monotone_approximation`). Sartor et
  al. (2025): monotone one-sided-saturating activations — `…saturating_interpolation` (Thm 3.5,
  ε-approximate) and `…nonpos_weight_universal` (Prop 3.11), tied together by the point-reflection /
  weight-sign–saturation equivalence (Props 3.8 & 3.10).
```

- [ ] **Step 2: Update the layout table — add a Monotone row, fix the root row.**
  In the layout table, add this row immediately after the Leshno row:

```markdown
| `NeuralNetworkProofs/UniversalApproximation/Monotone/` + `Monotone.lean` | `UniversalApproximation.Monotone` | the monotone-network development (Mikulincer–Reichman + Sartor et al.) |
```

  and change the root row's Contents cell from
  `root: re-exports both UAT roots so `lake build` verifies both headlines`
  to
  `root: re-exports the three UAT roots so `lake build` verifies all headlines`.

- [ ] **Step 3: Remove the stale "reserved for the future" sentence.**
  Delete the paragraph:
  `` `UniversalApproximation/Monotone/` (namespace `UniversalApproximation.Monotone`) is reserved for the future monotone-NN work. ``

- [ ] **Step 4: Verify no NEW over-long prose (layout-table rows are exempt — see Global
  Constraints).** Confirm the prose you added (the Monotone bullet in "What this is") wraps at ≤100,
  and that the only lines >100 in `CLAUDE.md` are Markdown **table** rows (`| … |`):
  Run: `awk 'length>100 && $0 !~ /^\|/ {print NR": "length}' CLAUDE.md`
  Expected: (empty — every >100 line is a table row).

- [ ] **Step 5: Commit.**

```bash
git add CLAUDE.md
git commit -m "docs: refresh CLAUDE.md for the completed Monotone development"
```

---

### Task 2: Complete the root module's headline list

**Files:**
- Modify: `NeuralNetworkProofs.lean` (the `/-! … -/` docstring, ~lines 11–24)

**Interfaces:** none (documentation; imports/build already correct).

- [ ] **Step 1: Add the three missing headlines to the docstring list.**
  The bullet list currently names 4 headlines. Make it name all 7 by (a) adding an
  `universal_approximation_eps` bullet right after the `universal_approximation` bullet, and (b)
  adding two Sartor bullets right after the `monotone_approximation` bullet. Final list:

```markdown
* `UniversalApproximation.Cybenko.universal_approximation` — Cybenko (1989).
* `UniversalApproximation.Cybenko.universal_approximation_eps` — Cybenko (1989), ε-approximate form.
* `UniversalApproximation.Leshno.leshno_dense_iff` — Leshno–Lin–Pinkus–Schocken (1993).
* `UniversalApproximation.Monotone.monotone_interpolation` — Mikulincer–Reichman (2022),
  interpolation form (Result 1).
* `UniversalApproximation.Monotone.monotone_approximation` — Mikulincer–Reichman (2022),
  approximation form (Result 1).
* `UniversalApproximation.Monotone.saturating_interpolation` — Sartor et al. (2025), Theorem 3.5
  (ε-approximate; monotone one-sided-saturating activations).
* `UniversalApproximation.Monotone.nonpos_weight_universal` — Sartor et al. (2025), Proposition 3.11.
```

- [ ] **Step 2: Verify the module still builds (docstring-only change).**
  Run: `lake build NeuralNetworkProofs.lean 2>/dev/null || lake build NeuralNetworkProofs`
  Expected: `Build completed successfully`, no errors/warnings.

- [ ] **Step 3: Verify line lengths ≤ 100 for the file.**
  Run: `python3 -c "print([ (i,len(l.rstrip(chr(10)))) for i,l in enumerate(open('NeuralNetworkProofs.lean'),1) if len(l.rstrip(chr(10)))>100 ])"`
  Expected: `[]`

- [ ] **Step 4: Commit.**

```bash
git add NeuralNetworkProofs.lean
git commit -m "docs(root): list all seven headlines in the re-export docstring"
```

---

### Task 3: Widen the CI blanket-import gate repo-wide

**Files:**
- Modify: `.github/workflows/ci.yml` (the "ForMathlib minimal-imports gate" step)

**Interfaces:** none (CI config).

- [ ] **Step 1: Replace the gate step.** Replace the entire `- name: ForMathlib minimal-imports
  gate` step (its `name` and `run` block) with the repo-wide version:

```yaml
      - name: Minimal-imports gate (no whole-library `import Mathlib`)
        run: |
          set -euo pipefail
          # Every source file must use minimal, specific Mathlib imports, never the whole-library
          # `import Mathlib` (it makes `lake build` much slower). Guards the whole tree.
          if grep -rn '^import Mathlib$' NeuralNetworkProofs/; then
            echo "::error::A file uses whole-library 'import Mathlib'; replace with minimal imports."
            exit 1
          fi
          echo "All files use minimal imports (no whole-library 'import Mathlib')."
```

- [ ] **Step 2: Simulate the gate locally (it must pass — repo is already clean).**
  Run: `if grep -rn '^import Mathlib$' NeuralNetworkProofs/; then echo FAIL; else echo "PASS (no blanket imports)"; fi`
  Expected: `PASS (no blanket imports)`

- [ ] **Step 3: Validate the YAML parses.**
  Run: `python3 -c "import yaml; yaml.safe_load(open('.github/workflows/ci.yml')); print('valid YAML')"`
  Expected: `valid YAML`

- [ ] **Step 4: Commit.**

```bash
git add .github/workflows/ci.yml
git commit -m "ci: widen minimal-imports gate from ForMathlib to the whole repo"
```

---

### Task 4: Whole-branch verify, push, and open the PR

**Files:** none (verification + git/gh).

**Interfaces:** consumes the commits from Tasks 1–3 plus the spec commit `a3ca038`.

- [ ] **Step 1: Full build, zero warnings.**
  Run: `lake build NeuralNetworkProofs 2>&1 | grep -iE "warning|error" && echo ISSUES || echo "clean"`
  Expected: `clean`

- [ ] **Step 2: Sorry-free gate — all 7 headlines axiom-clean.**
  Run: `lake env lean scripts/check_sorry_free.lean`
  Expected: 7 lines, each `depends on axioms: [propext, Classical.choice, Quot.sound]`; no `sorryAx`.

- [ ] **Step 3: Confirm the branch diff vs `main` is docs/CI only (no `.lean` proof changes).**
  Run: `git diff --stat origin/main..HEAD`
  Expected: only `CLAUDE.md`, `NeuralNetworkProofs.lean`, `.github/workflows/ci.yml`, and the spec
  markdown under `docs/superpowers/specs/`.

- [ ] **Step 4: Push the branch.**
  Run: `git push -u origin chore/resolve-loose-ends`
  Expected: new branch pushed, exit 0.

- [ ] **Step 5: Open the PR.**

```bash
gh pr create --base main --head chore/resolve-loose-ends \
  --title "chore: resolve doc + CI loose ends from the repo review" \
  --body "$(cat <<'EOF'
Closes the documentation and CI loose ends found in the whole-repo review (no proof/statement/axiom
changes):

- **CLAUDE.md** — refreshed for the completed Monotone development (three developments; Monotone in
  the layout table; drop the "next planned"/"reserved for the future" framing).
- **NeuralNetworkProofs.lean** — root docstring now lists all 7 headlines (was 4).
- **ci.yml** — the blanket-`import Mathlib` gate now covers the whole `NeuralNetworkProofs/` tree,
  not just `ForMathlib/` (locks in the repo-wide import minimization).

Verification: `lake build` green with zero warnings; `scripts/check_sorry_free.lean` — all 7
headlines `[propext, Classical.choice, Quot.sound]`; the widened import gate passes (no blanket
imports anywhere).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
```

  Expected: prints the PR URL. Confirm CI starts (`gh pr checks` shows the build job).

---

### Task 5: Prune stale local branches (local only — no PR)

**Files:** none (local git).

- [ ] **Step 1: List local branches to confirm targets.**
  Run: `git branch`
  Expected: `main`, `chore/resolve-loose-ends`, and ~10 stale branches
  (`feat/leshno-uat`, `feat/leshno-leaves-DA`, `feat/leshno-sorry-free`,
  `feat/monotone-saturating-uat`, `refactor/cybenko-leshno-imports`, `refactor/sartor-cosmetics`,
  `refactor/decouple-formathlib`, `refactor/formathlib-conformance`, `refactor/formathlib-phase2`,
  `refactor/neural-network-proofs`, `chore/remove-commit-signing`).

- [ ] **Step 2: Delete the merged branches (safe: 0 commits ahead of `main`).**

```bash
git branch -d feat/leshno-leaves-DA feat/leshno-sorry-free feat/monotone-saturating-uat \
  refactor/cybenko-leshno-imports refactor/sartor-cosmetics refactor/decouple-formathlib \
  refactor/formathlib-conformance refactor/formathlib-phase2 refactor/neural-network-proofs \
  chore/remove-commit-signing
```

  Expected: each reports `Deleted branch … (was <sha>)`. (`git branch -d` refuses any not merged into
  its upstream/HEAD — a safety net.)

- [ ] **Step 3: Force-delete the obsolete `feat/leshno-uat` (has unmerged obsolete commit
  `66a6375`).** Its lone commit is a design spec for already-filled Leshno leaves — intentionally
  discarded.

```bash
git branch -D feat/leshno-uat
```

  Expected: `Deleted branch feat/leshno-uat (was 66a6375)`.

- [ ] **Step 4: Confirm only `main` and the working branch remain.**
  Run: `git branch`
  Expected: `main` and `chore/resolve-loose-ends` only.

---

## Notes / out of scope

- Do **not** edit archival mentions of signing / "monotone planned" in `docs/superpowers/plans/*` or
  `.claude/skills/*` (historical records).
- Do **not** touch the GitHub "signed commits" ruleset (already disabled).
- No `.lean` proof, statement, or axiom changes anywhere.
