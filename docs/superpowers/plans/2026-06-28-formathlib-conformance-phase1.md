# ForMathlib Conformance — Phase 1 (mechanical) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan. Steps use checkbox (`- [ ]`) syntax. **Task 2 fans out to one concurrent agent per file in the shared checkout** (see Concurrency).

**Goal:** Bring the nine `NeuralNetworkProofs/ForMathlib/` files to Mathlib mechanical standards —
minimal specific imports (no `import Mathlib`), Apache-2.0 `LICENSE` + copyright headers, the
`minImports` linter enabled and clean, `mathlibStandardSet` lint-clean — behavior-preserving (no
statement/proof changes), and extend CI to fail on `ForMathlib` linter warnings.

**Architecture:** Shared-checkout concurrency. The 9 files are independent for this mechanical pass,
so Task 2 runs one agent per file **concurrently in the same working tree**; each agent edits only its
file and verifies via `lake env lean` / `#min_imports` (concurrent-safe *reads* of existing oleans —
no `lake build` lock). The controller does a single unified `lake build` + sorry-free axiom gate at
the end. (Worktrees were rejected: they don't share `.lake/build`, forcing a per-worktree Mathlib
re-fetch.)

**Tech Stack:** Lean 4 + Mathlib; `Mathlib.Tactic.MinImports` (`#min_imports`, `linter.minImports`);
Lake; GitHub Actions. Verification: `lake env lean <file>` (per file), `lake build` + `#print axioms`
via `lake env lean` (final).

## Global Constraints

- **Behavior-preserving:** no public statement, signature, or proof-body change. Only the
  `import Mathlib` line, added header, module-doc normalization, and `set_option linter.minImports true`
  may change. The `git diff` for each `.lean` file must touch only imports / header / docstring /
  `set_option` — never a `theorem`/`def`/`lemma` signature or proof body.
- Intra-`ForMathlib` imports (`import NeuralNetworkProofs.ForMathlib.X`) are **unchanged**; only the
  `import Mathlib` line is replaced with minimal `Mathlib.…` imports.
- Line length ≤ 100 codepoints.
- Commits SSH-signed (`git commit -S`) — if signing is unavailable (container rebuilds have wiped the
  key before), commit unsigned and re-sign the branch before the PR; do not block on it.
- No `sorry` introduced; behavior preserved means `#print axioms` on the downstream headlines
  (`UniversalApproximation.Leshno.leshno_dense_iff`, `UniversalApproximation.Cybenko.universal_approximation`)
  stays `[propext, Classical.choice, Quot.sound]`.
- Scope is `ForMathlib/` only; do not touch `Cybenko`/`Leshno`/`NeuralNetwork` (they still
  `import Mathlib`, so a repo-wide `minImports` linter is out of scope).

## Files (Phase 1)

The nine `NeuralNetworkProofs/ForMathlib/*.lean` (dependency order, leaves first):
`ConvolutionPolynomial`, `IteratedDerivPolynomial`, `RidgePowersSpan`, `RieszKantorovich`,
`SmoothCompactAntideriv`, `ConvolutionIteratedDeriv`, `PolynomialDistribution`,
`ConvolutionDegreeBound`, `UniformRiemannConvolution`. Plus root `LICENSE` and `.github/workflows/ci.yml`.

The copyright header (Mathlib layout — name only, no email), verbatim, as the FIRST lines of each file:

```lean
/-
Copyright (c) 2026 Davor Runje. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davor Runje
-/
```

---

### Task 1: Add `LICENSE`

**Files:** Create `LICENSE` (repo root).

- [ ] **Step 1: Write the Apache License 2.0 text** to `LICENSE` (the standard, unmodified Apache-2.0
  text; copyright line "Copyright 2026 Davor Runje"). Use the canonical text from
  https://www.apache.org/licenses/LICENSE-2.0.txt verbatim.

- [ ] **Step 2: Commit.**

```bash
git add LICENSE
git commit -S -m "chore: add Apache-2.0 LICENSE"
```

---

### Task 2: Per-file mechanical conformance (×9, run CONCURRENTLY)

**Files:** each `NeuralNetworkProofs/ForMathlib/<File>.lean` (one agent per file).

**Interfaces:** none cross-task; each file is independent for this pass. Public declaration names,
signatures, and proof bodies are unchanged.

**Concurrency:** the controller dispatches one agent per file **in parallel** (shared checkout).
Each agent: edits ONLY its assigned file; verifies with `lake env lean` / `#min_imports` (NOT
`lake build`, to avoid build-lock contention); does NOT commit (the controller commits all nine
together in Task 4 after the unified build). Run in a couple of waves (≈4–5 at a time) to bound
concurrent elaboration load.

**Per-file procedure (identical for all nine; the only parameter is the filename):**

- [ ] **Step 1: Discover minimal imports.** Temporarily append `#min_imports` as the last line of the
  file (the file currently does `import Mathlib`, so `Mathlib.Tactic.MinImports` is in scope). Run:

```bash
lake env lean NeuralNetworkProofs/ForMathlib/<File>.lean
```

`#min_imports` prints the minimal `import …` block needed for the file's declarations. It includes
the `Mathlib.…` modules actually used. (If `#min_imports` is unavailable, add
`import Mathlib.Tactic.MinImports` first, or use `set_option linter.minImports true` and read the
linter's suggested set from the build/elaboration output.)

- [ ] **Step 2: Replace the `import Mathlib` line** with the discovered minimal `Mathlib.…` imports
  (sorted), **keeping** any existing `import NeuralNetworkProofs.ForMathlib.…` lines. Remove the
  temporary `#min_imports` line.

- [ ] **Step 3: Add the copyright header** as the very first lines (above all imports), verbatim from
  the Files section above.

- [ ] **Step 4: Normalize the module docstring** to `/-! # <Title> … -/` placed immediately AFTER the
  imports. **Keep** the `Intended Mathlib home:` note (it is intentional). Do not change any
  declaration.

- [ ] **Step 5: Enable the minImports linter.** Add `set_option linter.minImports true` after the
  imports (before the first declaration / after the module docstring).

- [ ] **Step 6: Verify the file in isolation** (no `lake build`):

```bash
lake env lean NeuralNetworkProofs/ForMathlib/<File>.lean
```

Expected: elaborates with **no errors**, **no `minImports` warning** (imports are minimal), and no
`mathlibStandardSet`/style warnings (fix line lengths ≤100 codepoints, etc.). If `lake env lean`
reports a missing import, add the specific `Mathlib.…` module it names and re-run. Confirm no
declaration body changed: `git diff NeuralNetworkProofs/ForMathlib/<File>.lean` shows only
header/import/docstring/`set_option` hunks.

- [ ] **Step 7 (report only — no commit):** the agent reports its file's final import block and the
  `lake env lean` result; the controller commits in Task 4.

**Assigned files (one agent each):** `ConvolutionPolynomial`, `IteratedDerivPolynomial`,
`RidgePowersSpan`, `RieszKantorovich`, `SmoothCompactAntideriv`, `ConvolutionIteratedDeriv`,
`PolynomialDistribution`, `ConvolutionDegreeBound`, `UniformRiemannConvolution`.

---

### Task 3: Extend CI to fail on `ForMathlib` linter warnings

**Files:** Modify `.github/workflows/ci.yml`.

- [ ] **Step 1: Read the current workflow** to match its existing structure (the build job + the
  sorry-free axiom gate added in the reorg).

- [ ] **Step 2: Add a `ForMathlib` lint-warning gate.** After the build, elaborate each `ForMathlib`
  file and fail if any linter (especially `minImports`) warning is emitted. Concretely, a step that
  runs `lake env lean` on each `ForMathlib/*.lean` (or greps the build log scoped to
  `NeuralNetworkProofs/ForMathlib/`) and exits non-zero if the output contains `warning:`:

```yaml
      - name: ForMathlib lint gate (no warnings, incl. minImports)
        run: |
          set -euo pipefail
          fail=0
          for f in NeuralNetworkProofs/ForMathlib/*.lean; do
            out=$(lake env lean "$f" 2>&1) || { echo "$out"; fail=1; continue; }
            if echo "$out" | grep -q 'warning:'; then echo "::error::lint warning in $f"; echo "$out"; fail=1; fi
          done
          exit $fail
```

(Adjust to the actual workflow's runner/cache setup; keep the existing build + sorry-free steps.)

- [ ] **Step 3: Commit.**

```bash
git add .github/workflows/ci.yml
git commit -S -m "ci: fail on ForMathlib linter warnings (minImports enforcement)"
```

---

### Task 4: Unified build, axiom gate, and commit the conversions

**Files:** commits the nine `ForMathlib` files edited in Task 2.

- [ ] **Step 1: Full build.**

```bash
lake build
```
Expected: green. (If a concurrent-build EMFILE recurs — unlikely now that imports are minimal — fall
back to the serial per-module loop used in the reorg.) Fix any file whose minimal imports turned out
to be incomplete (add the specific `Mathlib.…` module the error names; re-run `lake env lean` on it).

- [ ] **Step 2: No `import Mathlib` remains; LICENSE + headers present.**

```bash
grep -rn '^import Mathlib$' NeuralNetworkProofs/ForMathlib/ && echo "STILL HAS import Mathlib" || echo "minimal-imports OK"
grep -L 'Copyright (c) 2026' NeuralNetworkProofs/ForMathlib/*.lean || echo "all have header"
test -f LICENSE && echo "LICENSE present"
```
Expected: `minimal-imports OK`, `all have header`, `LICENSE present`.

- [ ] **Step 3: Behavior-preservation axiom gate** (fresh oleans):

```bash
cat > /tmp/ck_conf.lean << 'EOF'
import NeuralNetworkProofs
open UniversalApproximation.Cybenko UniversalApproximation.Leshno
#print axioms universal_approximation
#print axioms leshno_dense_iff
EOF
lake env lean /tmp/ck_conf.lean
```
Expected: both `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

- [ ] **Step 4: Confirm diffs are mechanical-only.** For each ForMathlib file,
  `git diff --stat` and a spot `git diff` confirm only header/import/docstring/`set_option` lines
  changed — no declaration signature or proof body. If any proof body changed, revert that hunk.

- [ ] **Step 5: Commit the nine conversions.**

```bash
git add NeuralNetworkProofs/ForMathlib/*.lean
git commit -S -m "refactor(formathlib): minimal imports + headers + minImports linter (Phase 1)"
```

---

## Self-Review

**Spec coverage.** LICENSE → Task 1. Minimal imports + header + module-doc + `minImports` linter +
lint-clean (per file) → Task 2. CI warning-gate → Task 3. Build-green + axioms-unchanged + mechanical-
only diff + `set_option linter.minImports true` enabled & clean → Tasks 2/4. Phase-1 done-criteria all
mapped. Phase 2 (proof decomposition) is explicitly out of scope (separate PR).

**Placeholder scan.** No "TBD". The per-file procedure is written once and applied to all nine
(parameterized by filename) — this is DRY, not a "similar to Task N" omission. The CI step has a
concrete script with a noted adapt-to-runner caveat.

**Type/consistency.** No cross-task type interfaces (mechanical pass). The header text and the
`set_option linter.minImports true` line are identical across all nine files. The axiom-gate theorem
names match the post-reorg namespaces (`UniversalApproximation.Cybenko.universal_approximation`,
`UniversalApproximation.Leshno.leshno_dense_iff`).
