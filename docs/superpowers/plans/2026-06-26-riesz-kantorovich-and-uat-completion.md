# Riesz–Kantorovich + UAT Completion — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the Riesz–Kantorovich positive decomposition of an order-bounded functional on a real vector lattice (sorry-free, upstream-ready), then use it to close `riesz_repr` so the whole UAT is sorry-free.

**Architecture:** Part 1 (tasks 1–6) builds the decomposition bottom-up in a dependency-free `Contrib/RieszKantorovich.lean`; Part 2 (tasks 7–8) instantiates it at `C(↥K,ℝ)` and assembles a signed measure via positive `RealRMK`.

**Tech Stack:** Lean 4, Mathlib v4.32.0-rc1, lake, lean-lsp MCP tools.

## Global Constraints

- Branch `feat/riesz-kantorovich`. Spec: `docs/superpowers/specs/2026-06-26-riesz-kantorovich-and-uat-completion-design.md`.
- **Part 1 file** `LeanPlayground/Contrib/RieszKantorovich.lean`: `import Mathlib` only, **no playground imports**, Mathlib style (docstrings, ≤100-char lines, Mathlib naming), general typeclasses. It must be **fully `sorry`-free** — it is the contribution.
- **Vector-lattice setting** (pin exact instances at Task 1 via `lean_hover_info`/`lean_leansearch`): `variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E]`. Use `PosPart`/`NegPart` (`x⁺`, `x⁻`).
- **Per-task discipline (TDD analogue):** (a) write the declaration with `:= by sorry` / `:= sorry`, confirm the *statement* elaborates; (b) prove it, confirm no `sorry`; (c) `#print axioms <decl>` shows only `[propext, Classical.choice, Quot.sound]`; (d) commit. No accumulated sorries across commits.
- **Lean iteration expected.** Statements below are exact; proofs are strategy + named Mathlib lemmas. Load MCP tools (`ToolSearch "select:mcp__lean-lsp__lean_run_code,mcp__lean-lsp__lean_diagnostic_messages,mcp__lean-lsp__lean_leansearch,mcp__lean-lsp__lean_loogle,mcp__lean-lsp__lean_hover_info,mcp__lean-lsp__lean_goal"`) and iterate against the LSP.
- **No contingency admits in Part 1** (it's the contribution): if a step is intractable after sustained effort, report `BLOCKED` rather than shipping a `sorry`. The full `Lattice` instance (Task 6) is the *capstone*: if disproportionately heavy, it may be deferred with `exists_positive_decomposition` (Task 5) as the shipped deliverable — flag this explicitly, do not sorry it.
- Commit after each task; if signing hangs >~30s retry with `-c commit.gpgsign=false`.

---

### Task 1: File scaffold + Riesz decomposition property

**Files:** Create `LeanPlayground/Contrib/RieszKantorovich.lean`

**Interfaces — Produces:** `RieszKantorovich.riesz_decomp : 0 ≤ z → z ≤ x + y → 0 ≤ x → 0 ≤ y → ∃ a b, z = a + b ∧ 0 ≤ a ∧ a ≤ x ∧ 0 ≤ b ∧ b ≤ y`

- [ ] **Step 1: Scaffold + statement (with `sorry`)**
```lean
import Mathlib

/-!
# Riesz–Kantorovich decomposition (order-bounded dual of a vector lattice)
Intended Mathlib home: `Mathlib/Analysis/Order/` (confirm with maintainers).
-/

namespace RieszKantorovich

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]

/-- Riesz decomposition property: a positive element below a sum splits along the sum. -/
theorem riesz_decomp {x y z : E} (hz : 0 ≤ z) (hzxy : z ≤ x + y) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ a b, z = a + b ∧ 0 ≤ a ∧ a ≤ x ∧ 0 ≤ b ∧ b ≤ y := by
  sorry

end RieszKantorovich
```

- [ ] **Step 2: Confirm the statement elaborates** (`lean_diagnostic_messages`: only `sorry` warning). Also `#check`/`lean_hover_info` to confirm the typeclass bundle for the *module* parts you'll add in Task 2 (`Module ℝ E`, `PosSMulMono ℝ E`, `OrderedSMul ℝ E`) — record the exact working bundle.

- [ ] **Step 3: Prove.** Set `a := z ⊓ x`, `b := z - a`. Then `0 ≤ a` (`le_inf hz hzx?`... use `le_inf`), `a ≤ x` (`inf_le_right`), `z = a + b` (`add_sub_cancel`), `0 ≤ b` and `b ≤ y` from `z ≤ x + y` and lattice identities (`b = z - z⊓x = z - z⊓x`; use `sub_nonneg`, `inf_le_left`, and `z ⊓ x + z ⊔ x = z + x`-style lemmas — search `lean_leansearch "z - z ⊓ x"`, `inf_le_left`, `le_sub_iff_add_le`). Key: `b ≤ y` follows from `z ≤ x + y ⇒ z - x ≤ y` and `b = z - z⊓x ≤ z - ... `; iterate with `lean_goal`.

- [ ] **Step 4: Verify** — no errors, no `sorry`; `#print axioms riesz_decomp` clean.

- [ ] **Step 5: Commit**
```bash
git add LeanPlayground/Contrib/RieszKantorovich.lean
git commit -m "feat(rk): file scaffold + Riesz decomposition property"
```

---

### Task 2: `IsOrderBounded` + `rkSup` + well-definedness

**Interfaces — Consumes:** Task 1 setting. **Produces:**
- `IsOrderBounded (L : E →ₗ[ℝ] ℝ) : Prop := ∀ f : E, 0 ≤ f → BddAbove {y : ℝ | ∃ g, 0 ≤ g ∧ g ≤ f ∧ L g = y}`
- `rkSup (L : E →ₗ[ℝ] ℝ) (f : E) : ℝ := sSup {y : ℝ | ∃ g, 0 ≤ g ∧ g ≤ f ∧ L g = y}`
- `rkSup_nonneg`, `le_rkSup` (`0≤g→g≤f→ L g ≤ rkSup L f`), `rkSup_le` (universal property).

- [ ] **Step 1: Add `Module ℝ E` etc. to `variable`; write defs + lemma statements (sorries).**
```lean
variable [Module ℝ E] [PosSMulMono ℝ E]

def IsOrderBounded (L : E →ₗ[ℝ] ℝ) : Prop :=
  ∀ f : E, 0 ≤ f → BddAbove {y : ℝ | ∃ g, 0 ≤ g ∧ g ≤ f ∧ L g = y}

noncomputable def rkSup (L : E →ₗ[ℝ] ℝ) (f : E) : ℝ :=
  sSup {y : ℝ | ∃ g, 0 ≤ g ∧ g ≤ f ∧ L g = y}

theorem le_rkSup (L : E →ₗ[ℝ] ℝ) {f g : E} (hL : IsOrderBounded L)
    (hf : 0 ≤ f) (hg0 : 0 ≤ g) (hgf : g ≤ f) : L g ≤ rkSup L f := by sorry

theorem rkSup_nonneg (L : E →ₗ[ℝ] ℝ) {f : E} (hf : 0 ≤ f) : 0 ≤ rkSup L f := by sorry

theorem rkSup_le (L : E →ₗ[ℝ] ℝ) {f : E} {c : ℝ}
    (h : ∀ g, 0 ≤ g → g ≤ f → L g ≤ c) : rkSup L f ≤ c := by sorry
```

- [ ] **Step 2: Confirm statements elaborate.**

- [ ] **Step 3: Prove.** The set `S f := {y | ∃ g, 0≤g≤f ∧ L g = y}` is nonempty (`g = 0`: `L 0 = 0 ∈ S f`, using `map_zero`) and, under `hL`, `BddAbove`. So:
  - `le_rkSup`: `le_csSup (hL f hf) ⟨g, hg0, hgf, rfl⟩`.
  - `rkSup_nonneg`: `0 = L 0 ≤ rkSup L f` via `le_rkSup` with `g = 0` (`map_zero`, `hf`).
  - `rkSup_le`: `csSup_le ⟨0, …nonempty…⟩ (fun y ⟨g, hg0, hgf, rfl⟩ => h g hg0 hgf)`.
  Search: `le_csSup`, `csSup_le`, `Set.Nonempty`.

- [ ] **Step 4: Verify** (`#print axioms` on each).

- [ ] **Step 5: Commit**
```bash
git add LeanPlayground/Contrib/RieszKantorovich.lean
git commit -m "feat(rk): order-bounded predicate, rkSup, and its sup lemmas"
```

---

### Task 3: `rkSup` additivity on the positive cone (crux)

**Interfaces — Consumes:** `riesz_decomp`, `rkSup`, `le_rkSup`, `rkSup_le`. **Produces:**
`rkSup_add : IsOrderBounded L → 0 ≤ f₁ → 0 ≤ f₂ → rkSup L (f₁ + f₂) = rkSup L f₁ + rkSup L f₂`

- [ ] **Step 1: Statement (with `sorry`)**
```lean
theorem rkSup_add (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f₁ f₂ : E}
    (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) :
    rkSup L (f₁ + f₂) = rkSup L f₁ + rkSup L f₂ := by sorry
```

- [ ] **Step 2: Confirm it elaborates.**

- [ ] **Step 3: Prove by `le_antisymm`.**
  - **(≤)** `rkSup_le`: take `g` with `0≤g≤f₁+f₂`; by `riesz_decomp` split `g = a + b`, `0≤a≤f₁`, `0≤b≤f₂`; then `L g = L a + L b ≤ rkSup L f₁ + rkSup L f₂` (`map_add`, `le_rkSup` twice).
  - **(≥)** For `g₁≤f₁`, `g₂≤f₂` positive: `g₁+g₂ ≤ f₁+f₂` and `L g₁ + L g₂ = L (g₁+g₂) ≤ rkSup L (f₁+f₂)` (`le_rkSup`). So `rkSup L f₁ + rkSup L f₂ ≤ rkSup L (f₁+f₂)` by taking sup over `g₁,g₂` — formally: `rkSup L f₁ ≤ rkSup L (f₁+f₂) - rkSup L f₂`-style via two `csSup_le`/`le_csSup` steps, or `add_le_of_le_sub` patterns. Iterate with `lean_goal`; search `csSup_add_le`/`Real.add_sSup`-style or do the two-variable sup manually.

- [ ] **Step 4: Verify** (`#print axioms rkSup_add`).

- [ ] **Step 5: Commit**
```bash
git add LeanPlayground/Contrib/RieszKantorovich.lean
git commit -m "feat(rk): rkSup is additive on the positive cone"
```

---

### Task 4: Homogeneity + the linear functional `Lpos`

**Interfaces — Consumes:** `rkSup`, `rkSup_add`, `rkSup_nonneg`. **Produces:**
- `rkSup_smul : 0 ≤ c → 0 ≤ f → rkSup L (c • f) = c * rkSup L f`
- `Lpos (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) : E →ₗ[ℝ] ℝ` with `Lpos_apply_of_nonneg : 0 ≤ f → Lpos L hL f = rkSup L f`.

- [ ] **Step 1: Statements (with `sorry`)**
```lean
theorem rkSup_smul (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {c : ℝ} (hc : 0 ≤ c)
    {f : E} (hf : 0 ≤ f) : rkSup L (c • f) = c * rkSup L f := by sorry

noncomputable def Lpos (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) : E →ₗ[ℝ] ℝ where
  toFun x := rkSup L x⁺ - rkSup L x⁻
  map_add' := by sorry
  map_smul' := by sorry
```

- [ ] **Step 2: Confirm statements elaborate** (the `LinearMap` fields are the obligations).

- [ ] **Step 3: Prove.**
  - `rkSup_smul`: for `c ≥ 0`, the map `g ↦ c • g` is an order-isomorphism of `[0,f]` onto `[0,c•f]` (uses `PosSMulMono`/`smul_nonneg`, `smul_le_smul_of_nonneg_left`), and `L (c•g) = c * L g` (`map_smul`); push through `sSup` (`Real.sSup_smul`-style or `csSup` image lemmas; handle `c = 0` separately via `rkSup_nonneg` and `zero_smul`). Search `lean_leansearch "sSup of scalar multiple set"`.
  - `Lpos.map_add'`: the key identity. For all `x y`, using `x⁺,x⁻` and `rkSup_add`: reduce `rkSup` of positive parts. Standard route: show the difference `rkSup L a⁺ - rkSup L a⁻` defines an additive map because `rkSup` is additive on the cone and every element is a difference of positives; concretely prove `Lpos (x+y) = Lpos x + Lpos y` via `(x+y)⁺ + x⁻ + y⁻ = (x+y)⁻ + x⁺ + y⁺` (a lattice identity) + `rkSup_add` on both sides. Search the lattice identity (`posPart_add_negPart`, `posPart_sub_negPart`).
  - `Lpos.map_smul'`: from `rkSup_smul` for `c≥0` and the `x⁺/x⁻` swap for `c<0` (`(c•x)⁺ = (-c)•x⁻` etc.).

- [ ] **Step 4: Verify** (`#print axioms Lpos`, `rkSup_smul`).

- [ ] **Step 5: Commit**
```bash
git add LeanPlayground/Contrib/RieszKantorovich.lean
git commit -m "feat(rk): positive-homogeneity and the linear functional Lpos"
```

---

### Task 5: `exists_positive_decomposition` (headline deliverable)

**Interfaces — Consumes:** `Lpos`, `rkSup_nonneg`, `le_rkSup`. **Produces:**
`exists_positive_decomposition (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) : ∃ Lp Lm : E →ₗ[ℝ] ℝ, (∀ f, 0 ≤ f → 0 ≤ Lp f) ∧ (∀ f, 0 ≤ f → 0 ≤ Lm f) ∧ ∀ x, L x = Lp x − Lm x`

- [ ] **Step 1: Supporting lemmas + headline (with `sorry`)**
```lean
theorem Lpos_nonneg (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f : E} (hf : 0 ≤ f) :
    0 ≤ Lpos L hL f := by sorry

theorem le_Lpos (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) {f : E} (hf : 0 ≤ f) :
    L f ≤ Lpos L hL f := by sorry

theorem exists_positive_decomposition (L : E →ₗ[ℝ] ℝ) (hL : IsOrderBounded L) :
    ∃ Lp Lm : E →ₗ[ℝ] ℝ,
      (∀ f, 0 ≤ f → 0 ≤ Lp f) ∧ (∀ f, 0 ≤ f → 0 ≤ Lm f) ∧ ∀ x, L x = Lp x - Lm x := by
  sorry
```

- [ ] **Step 2: Confirm statements elaborate.**

- [ ] **Step 3: Prove.**
  - `Lpos_nonneg`: `0 ≤ f ⇒ Lpos L hL f = rkSup L f ≥ 0` (`Lpos_apply_of_nonneg` + `rkSup_nonneg`).
  - `le_Lpos`: `0 ≤ f ⇒ L f ≤ rkSup L f = Lpos L hL f` (`le_rkSup` with `g = f`).
  - `exists_positive_decomposition`: `Lp := Lpos L hL`, `Lm := Lpos L hL - L` (linear-map subtraction). Positivity of `Lm` on `f≥0` is `le_Lpos` (`0 ≤ Lpos f - L f`). `L x = Lp x - Lm x` is `sub_sub_cancel`.

- [ ] **Step 4: Verify** (`#print axioms exists_positive_decomposition` ⇒ clean).

- [ ] **Step 5: Commit**
```bash
git add LeanPlayground/Contrib/RieszKantorovich.lean
git commit -m "feat(rk): exists_positive_decomposition for order-bounded functionals"
```

---

### Task 6 (capstone): `Lattice` instance on the order-bounded dual

**Interfaces — Consumes:** all of Part 1. **Produces:** `OrderBoundedDual E` (subtype `{L // IsOrderBounded L}`) with its order and a `Lattice` instance whose `⊔` is given by the RK formula (`(L ⊔ M) f = rkSup (M - L) f + L f` on the cone, i.e. `L ⊔ M = L + Lpos (M - L)`).

- [ ] **Step 1: Define the type, order, and the join; state the `Lattice` instance (fields `sorry`).** (Exact `structure`/`def` and instance skeleton; the join is `L + Lpos (M-L)`, requiring `IsOrderBounded` closure under `+`, `-` — prove those as helper lemmas `IsOrderBounded.add`, `IsOrderBounded.sub` first.)

- [ ] **Step 2: Confirm elaboration.**

- [ ] **Step 3: Prove the lattice axioms** (`le_sup_left/right`, `sup_le`, and `⊓` dually via `L ⊓ M = -((-L) ⊔ (-M))` or `L + M - (L ⊔ M)`). Iterate; this is the heaviest task. **If after sustained effort the full instance is intractable, STOP and report — ship Tasks 1–5 (`exists_positive_decomposition`) as the deliverable and record the lattice instance as future work. Do NOT `sorry` it into the file.**

- [ ] **Step 4: Verify** (`#print axioms` on the instance / join lemmas).

- [ ] **Step 5: Commit**
```bash
git add LeanPlayground/Contrib/RieszKantorovich.lean
git commit -m "feat(rk): Lattice instance on the order-bounded dual (RK formula)"
```

---

### Task 7 (Part 2): `C(↥K,ℝ)` instances + order-bounded bridge

**Files:** Modify `LeanPlayground/UniversalApproximation/Riesz.lean` (add a private section above `riesz_repr`)

**Interfaces — Consumes:** `RieszKantorovich.IsOrderBounded`. **Produces:** `continuous_isOrderBounded : (L : C(↥K,ℝ) →L[ℝ] ℝ) → RieszKantorovich.IsOrderBounded L.toLinearMap` (with `↥K` compact).

- [ ] **Step 1: Add `import LeanPlayground.Contrib.RieszKantorovich`; confirm `C(↥K,ℝ)` vector-lattice + ordered-module instances resolve** (`ContinuousMap.instLattice`, module, `IsOrderedAddMonoid`, `PosSMulMono`). If any instance is missing for the compact subtype, derive it (search `lean_leansearch "ContinuousMap lattice ordered"`). Write `continuous_isOrderBounded` with `sorry`.

- [ ] **Step 2: Confirm elaboration.**

- [ ] **Step 3: Prove `continuous_isOrderBounded`.** For `f ≥ 0` and `0 ≤ g ≤ f`: `‖g‖ ≤ ‖f‖` (sup norm on compact, `0 ≤ g ≤ f ⇒ |g x| ≤ |f x| ≤ ‖f‖`; search `ContinuousMap.norm_le`, `abs_le_of_…`), so `|L g| ≤ ‖L‖ * ‖f‖` (`L.le_opNorm`), giving `BddAbove` by the constant `‖L‖ * ‖f‖`.

- [ ] **Step 4: Verify** (`lean_diagnostic_messages`; `#print axioms continuous_isOrderBounded`).

- [ ] **Step 5: Commit**
```bash
git add LeanPlayground/UniversalApproximation/Riesz.lean
git commit -m "feat(uat): C(K) vector-lattice instances + continuous ⇒ order-bounded"
```

---

### Task 8 (Part 2): Close `riesz_repr` + full build

**Files:** Modify `LeanPlayground/UniversalApproximation/Riesz.lean` (replace the `sorry` in `riesz_repr`)

**Interfaces — Consumes:** `exists_positive_decomposition`, `continuous_isOrderBounded`, positive `RealRMK`. **Produces:** proved `riesz_repr` (signature unchanged).

- [ ] **Step 1: Replace `riesz_repr`'s proof with a `sorry`-bodied skeleton** following the assembly; confirm it elaborates with exactly one `sorry`.

- [ ] **Step 2: Prove the assembly.**
  - `exists_positive_decomposition L.toLinearMap (continuous_isOrderBounded L)` ⇒ `Lp, Lm` positive linear functionals with `L g = Lp g − Lm g`.
  - Bridge each positive functional to `CompactlySupportedContinuousMap ↥K ℝ →ₚ[ℝ] ℝ` (compact ⇒ `ContinuousMap ≃ CompactlySupportedContinuousMap`; find the equiv/coercion via `lean_leansearch "CompactlySupportedContinuousMap compact space"`). Apply `RealRMK.rieszMeasure` ⇒ regular `μp, μn`; `RealRMK.integral_rieszMeasure` ⇒ `∫ g ∂μp = Lp g`, `∫ g ∂μn = Lm g`.
  - `μ := μp.toSignedMeasure - μn.toSignedMeasure`. Prove `signedIntegral μ g = ∫ g ∂μp − ∫ g ∂μn` (signed-measure integral is independent of the finite-measure-difference representation; relate the Jordan parts of `μ` to `μp, μn` via `MeasureTheory.SignedMeasure.toSignedMeasure_sub`-style lemmas; search). Hence `L g = signedIntegral μ g`.
  - `L = 0 ↔ μ = 0`: `μ = 0 ⇒ L = 0` is immediate; converse: `L = 0 ⇒ ∫ g ∂μp = ∫ g ∂μn ∀g ⇒ μp = μn` (`RealRMK.integralPositiveLinearMap_inj` or `FiniteMeasure.ext_of_forall_integral_eq`) `⇒ μ = 0`.
- [ ] **Step 3: Full build + axiom + sorry sweep.** `cd /workspaces/lean-playground && source "$HOME/.elan/env" && lake build 2>&1 | tail -40` must succeed. `#print axioms UniversalApproximation.riesz_repr` ⇒ only `[propext, Classical.choice, Quot.sound]`. `grep -rn "sorry" LeanPlayground` ⇒ no code `sorry` anywhere (UAT fully closed). `#check @UniversalApproximation.riesz_repr` ⇒ unchanged signature.

- [ ] **Step 4: Commit**
```bash
git add LeanPlayground/UniversalApproximation/Riesz.lean
git commit -m "feat(uat): close riesz_repr via Riesz-Kantorovich + positive RMK; UAT now sorry-free"
```

---

## Self-Review (completed by plan author)

- **Spec coverage:** Part 1 lemma chain → Tasks 1 (riesz_decomp), 2 (rkSup/well-def), 3 (additivity), 4 (homogeneity+Lpos), 5 (exists_positive_decomposition); Lattice capstone → Task 6. Part 2 instances+bridge → Task 7; RealRMK assembly + close riesz_repr → Task 8. Verification (sorry-free, `#print axioms`, signature unchanged) → Task 8 Step 3. ✓
- **Placeholder scan:** the only `sorry`s are the deliberate statement-first steps, each followed by a prove step; no "TODO"/"handle edge cases". Task 6 has an explicit *report-don't-sorry* contingency.
- **Type consistency:** `IsOrderBounded`, `rkSup`, `Lpos L hL`, `exists_positive_decomposition` signatures match across tasks; Task 7 feeds `L.toLinearMap` into `IsOrderBounded` (the predicate is on `E →ₗ[ℝ] ℝ`); Task 8 consumes `exists_positive_decomposition` + `continuous_isOrderBounded` exactly as Task 5/7 produce them.
- **Known risk:** Tasks 3 (additivity), 4 (`Lpos` linearity), 6 (lattice instance), and 8 (signed-measure-difference identity + compact-support bridge) are the hard cores. Each has named-lemma strategies and an iterate-against-LSP step. Part 1 must stay sorry-free (it is the contribution) — `BLOCKED` is the escape hatch, not a `sorry`.
