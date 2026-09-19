# Consult: local total-variation upgrade of exact Laplace-family agreement (germbij / laplace Lean)

## Context
Lean 4 + Mathlib. Losses `L₁ L₂ : ℝ^d → ℝ`, `C^∞`, nonnegative. `I_i(φ, t) = ∫ φ e^{-tL_i}`. `SuperPoly f := ∀ N, f = o(t^{-N})` at `t → ∞`.
Merged today: projective agreement (`I₂(φ) − C(t) I₁(φ)` SuperPoly for all `φ ∈ C_c^∞`) plus local equality of the losses near one C² zero ⇒ `C = 1 + o(t^{-∞})` and **exact** agreement `SuperPoly (I₂(φ) − I₁(φ))` for every `φ ∈ C_c^∞`. Your previous consult recommended the upgrade to continuous tests via local total variation, with the mechanism `|a − b|² ≤ t D (a − b)`, `a = e^{-tL₁}`, `b = e^{-tL₂}`, `D = L₂ − L₁`, tested at the smooth observable `η² D`.

## Plan (Lean-flavoured)
(P) For `x, y ≥ 0`: `|e^{-x} − e^{-y}| ≤ |x − y|` (via `1 − e^{-u} ≤ u` and `e^{-x} ≤ 1`) and `(y − x)(e^{-x} − e^{-y}) ≥ 0`. Hence, for `t ≥ 0`, `D (a − b) ≥ 0` and `|a − b|² ≤ t D (a − b)` pointwise.
(V) For a smooth compactly supported `η`: `E(t) := ∫ η² D (a − b) = I₁(η² D) − I₂(η² D)` is SuperPoly (the observable `η² D` is `C_c^∞` because the losses are smooth) and `E ≥ 0`. To avoid Hölder/Cauchy–Schwarz and square roots in Lean, I plan the AM–GM trick with a free parameter: for every `N`, pointwise `|a − b| ≤ t^{-N}/2 + t^{N} |a − b|²/2 ≤ t^{-N}/2 + t^{N+1} D(a − b)/2`, so `∫ η² |a − b| ≤ (∫ η²) t^{-N}/2 + t^{N+1} E(t)/2 ≤ C_N t^{-N}` eventually. Since this holds for every `N`, `∫ η² |a − b|` is SuperPoly. (Helper: `(∀ N, ∃ C, eventually |f| ≤ C t^{-N}) → SuperPoly f`.)
(U) For `φ` bounded by `M`, measurable, compactly supported: choose a `ContDiffBump` at `0` equal to `1` on a closed ball containing `tsupport φ`; then `|I₂(φ) − I₁(φ)| ≤ M ∫ η² |a − b|`, hence SuperPoly. Continuous compactly supported `φ` as a corollary (bounded by compactness).
(C) Wire into the closure package: projective agreement on `C_c^∞` + one common analytic zero ⇒ exact agreement on `C_c^0` and on bounded measurable compactly supported tests; the `1/Z` headline gains that conclusion.

## Questions
1. Is (P)–(U) correct as stated, and is the AM–GM route with `ε = t^{-N}` a faithful substitute for the Cauchy–Schwarz step (it seems to lose nothing at the SuperPoly level)? Any hidden integrability requirement (`η²|a−b|`, `η²|a−b|²` are continuous with compact support, so fine)?
2. Is smoothness of BOTH losses genuinely needed (so that `η² D ∈ C_c^∞` is in the tested class)? If the tested class were `C_c^k` for finite `k`, `C^k` losses would do; but with the seabed's `C_c^∞` hypothesis class there is no way around `C^∞` losses — correct?
3. Is there a stronger or cleaner target nearby? E.g. (a) the total variation over the whole space with a weight (`∫ |a − b| η²` for η just continuous?) — no, η²D must be smooth; (b) uniform-in-`t` local `L¹` control, i.e. the statement `∀ K compact, ∫_K |e^{-tL₂} − e^{-tL₁}| = o(t^{-∞})` with `1_K` rather than `η²` (follows from (V) with `η = 1` on `K`, since `|a−b| 1_K ≤ η²|a−b|`); (c) an `L^∞`-type statement is false in general? (d) agreement of the normalized expectations `⟨φ⟩` themselves for bounded measurable φ, i.e. `I₂(φ)/Z₂ − I₁(φ)/Z₁` SuperPoly given `Z_i ≳ t^{-d/2}` (the anchor) — is that a one-liner from (U) + `Z₂/Z₁ − 1` SuperPoly + the polynomial lower bound on `Z₁`?
4. Pitfalls in Lean you foresee for (P): is there a Mathlib lemma for `|exp(-x) − exp(-y)| ≤ |x − y|` on the nonnegative half-line (Lipschitz constant 1 of `exp` on `(-∞, 0]`), or is the two-line argument via `Real.add_one_le_exp` the way?
5. Vote: P+V+U+C as one tide (~300 lines)?
Numbered answers, statement-level Lean shapes; one-line vote at the end.
