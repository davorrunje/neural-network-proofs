# Results Website — design

**Goal:** A GitHub Pages website presenting the three formalized universal-approximation (UAT)
developments — Cybenko, Leshno, and Monotone (Mikulincer–Reichman + Sartor) — with **human-readable
statements and proofs shown alongside the formal Lean**, for a general technical audience.

**Approach (chosen: A, delivered all-in):** a `leanblueprint` (human-readable LaTeX math + prose
proofs + a clickable dependency graph, cross-linked to the Lean) **plus** `doc-gen4` (the formal API
for every declaration) **plus** a landing page — all built and deployed to GitHub Pages by a single
GitHub Actions workflow.

## Audience & scope

- **Audience:** general technical — accessible intros (what each UAT says and why formalizing it
  matters) with full mathematical rigor and the formal proofs one click away.
- **Blueprint prose (statements + proofs) covers all three developments' headlines + their key
  supporting lemmas;** `doc-gen4` covers *every* declaration. Indicative coverage:
  - *Cybenko:* `universal_approximation` (+ `universal_approximation_eps`); key lemmas — sigmoidal
    functions are discriminatory, and the Hahn–Banach / Riesz–Markov density argument.
  - *Leshno:* `leshno_dense_iff`; key lemmas — the class `M`, the polynomial / non-polynomial
    dichotomy, and the mollification + ridge-function density steps.
  - *Monotone:* `monotone_interpolation`, `monotone_approximation` (M-R); `saturating_interpolation`
    (Sartor Thm 3.5), `nonpos_weight_universal` (Prop 3.11), Prop 3.8 (`reflect`), Prop 3.10;
    key lemmas — Def 3.3 saturation, Lemma 3.6, Lemma 3.7, `approx_interior_value`, and
    the γ-normalized read-out engine.

## Site structure (GitHub Pages project site)

Base URL `https://davorrunje.github.io/neural-network-proofs/`:

- **`/` — landing page:** overview; the three developments with a one-line significance each; the
  sorry-free / axiom-clean guarantee; links to the blueprint, the API docs, the repo, and the source
  papers.
- **`/blueprint/` — the blueprint:** a short intro, then a chapter per development (definitions,
  statements, prose proofs), with the **dependency graph** at `/blueprint/dep_graph.html`.
- **`/docs/` — `doc-gen4` formal API:** every declaration, with precise statements, types, and
  source links.

## Human + formal, together

- Each blueprint result carries the **informal statement + prose proof**, tagged `\lean{DeclName}` +
  `\leanok`, linking to its declaration (`doc-gen4`) and source, with a "✓ formalized" marker.
- **Enhancement:** embed the formal Lean statement inline (a small code block) beneath the prose
  statement; the full formal (tactic) proof stays one click away via the `doc-gen4`/source link (not
  duplicated in the blueprint).
- The **dependency-graph** nodes are colored by state (statement / proof / formalized), visibly
  showing Sartor building on Mikulincer–Reichman and the shared activation-generic core.

## Toolchain & repo layout

- **`blueprint/`** — a `leanblueprint` project (`blueprint/src/*.tex`: `content.tex`, macros,
  per-chapter files) producing the plasTeX web build + the dependency graph.
- **`lakefile.toml`** — add `doc-gen4` as a dev dependency and build its docs facet.
- **Landing page** — a small static `index` (hand-written HTML/Markdown) assembled at deploy time.
- **`.github/workflows/`** — a new Pages workflow: build the Lean project (cached Mathlib), build
  `doc-gen4`, build the blueprint (LaTeX + plasTeX), assemble `/`, `/blueprint/`, `/docs/` into one
  site artifact, and deploy with `actions/deploy-pages`. Pages source = "GitHub Actions".

## Build & deploy (all-in)

- One workflow builds **everything** and deploys, on push to `main` and on manual dispatch.
- `doc-gen4` documents the whole import closure (**incl. Mathlib**) → slow, large build; accepted
  as the cost of "all-in". Mitigate with the Mathlib doc cache + Lake cache; the blueprint + landing
  are light.
- The existing `ci.yml` (build + sorry-free gate + minimal-imports gate) remains the **correctness**
  gate on PRs; the new workflow is a separate **deployment** pipeline. They do not overlap.

## Content authoring

- Blueprint prose is authored from the existing Lean **docstrings** + the **source papers** (Cybenko
  1989; Leshno–Lin–Pinkus–Schocken 1993; Mikulincer–Reichman 2022; Sartor et al. 2025) —
  **faithfully**, carrying over the honest deviation notes in the code (e.g. Thm 3.5's ε-approximate
  form vs the paper's λ→∞ idealization; the `σ` non-constant hypotheses; the Case-1 / reflect-dual
  scope).
- `\lean{}` / `\leanok` tags reference real declaration names; `leanblueprint`'s `checkdecls`
  verifies every referenced declaration exists in the built project.

## Verification / success criteria

- `leanblueprint` builds the web blueprint + dependency graph; `checkdecls` passes (no undefined
  `\lean` references).
- `doc-gen4` builds; the API site includes all seven headline declarations.
- The Pages workflow deploys; the live site serves `/`, `/blueprint/`, `/docs/` with working
  cross-links (landing → blueprint → formal declaration → source).
- Blueprint content faithfully matches the formalized statements (no overclaiming; deviation notes
  carried over).
- The existing `ci.yml` correctness gate stays green (site work does not touch the Lean proofs).

## Out of scope

- No changes to Lean proofs or theorem statements (the site is additive: `blueprint/`, `lakefile`
  docs facet, a Pages workflow, a landing page).
- Interactive / live Lean goal-state rendering (Verso / alectryon) — not this iteration.
- A custom domain — use the default `github.io` project URL.

## Risks

- **`doc-gen4` CI heaviness / time** — mitigated with caching; accepted (all-in).
- **Blueprint authoring effort** — prose proofs for the headlines + key lemmas across three
  developments is the bulk of the work.
- **Faithfulness of the prose to the formal statements** — mitigated by `checkdecls` and by carrying
  over the code's existing deviation notes rather than restating the papers uncritically.
