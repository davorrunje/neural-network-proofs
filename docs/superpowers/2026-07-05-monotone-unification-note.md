# Phase 1 Monotone-NN Unification Note (2026-07-05)

Phase 1 (`feat/monotone-saturating-uat`) generalized the merged M-R development (PR #16) to an
activation-generic model (`ActStack`) + an `IsEpsIndicator` gadget engine; the threshold gadget
(ε=0) re-derives `monotone_interpolation` exactly; sets up Phase 2 (Sartor Thm 3.5) / Phase 3
(Props 3.10/3.11). The ε-general all-layers engine is deferred to Phase 2 (discontinuous
`revPrefixLayer`).
