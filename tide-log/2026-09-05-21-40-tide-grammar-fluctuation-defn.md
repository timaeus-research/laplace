# Tide: grammar §4 fluctuation function — definition, integrability, base value

**Direction (user):** autoformalise the grammar paper (*Expectations and the exceptional
divisor*) on auto. Stage-1 campaign; this unit opens §4 (Fluctuations) in the `laplace` seabed.
**Seabed:** laplace, commit 60504c0 (branch tide/grammar-fluctuation-defn off main).
**Started:** 2026-09-05

## Context

The grammar paper §4 derives the `Z_n[φ] ∼ ∑ C_{μ,m} n^{-μ}(log n)^{m-1}` expansion via
Watanabe's **fluctuation function** (Def 5.8; grammar `eq:fluctuation`):

  `S_λ(a) = ∫₀^∞ t^{λ-1} e^{-β t + β a √t} dt`,  `β, λ > 0`.

§4 is virgin in laplace (no fluctuation/Weber/Hermite modules). This is the foundational first
unit; `lem:fluctuation_properties` (i)–(iv), `prop:fluctuation_weber`, `cor:fluctuation_closed_form`
(parabolic cylinder), ladder algebra follow in subsequent units.

## Target (this unit) — `Laplace/Grammar/Fluctuation.lean`

- `def fluctuation (β lam a : ℝ) := ∫ t in Ioi 0, t^(lam-1) * exp(-β t + β a √t)`
- `fluctuation_integrableOn (hβ)(hlam)(a) : IntegrableOn (…) (Ioi 0)` — integrable ∀ a.
- `fluctuation_zero (hβ)(hlam) : fluctuation β lam 0 = β^(-lam) * Γ(lam)`.

Skeleton typechecks (lean-state: only the two `sorry` warnings).

## Proof plan

- **Base value:** at `a=0` the integrand is `t^(lam-1) e^{-β t}`; `integral_rpow_mul_exp_neg_mul_rpow`
  (Mathlib `Integral/Gamma`) at `p=1, q=lam-1, b=β` gives `β^(-(lam)/1)·(1/1)·Γ(lam) = β^(-lam)Γ(lam)`.
  Reconcile `-β t` ↔ `-β·t^(1:ℝ)` via `rpow_one`.
- **Integrability:** AM–GM `a√t ≤ t/2 + a²/2` (i.e. `(√t-a)²≥0`) ⇒ `e^{-βt+βa√t} ≤ e^{βa²/2} e^{-(β/2)t}`,
  so dominate by `C·t^(lam-1) e^{-(β/2)t}` with `C=e^{βa²/2}`; the majorant is
  `integrableOn_rpow_mul_exp_neg_mul_rpow (hs:=lam-1)(hp:=1)(hb:=β/2)`. Via `Integrable.mono'`.

## Numerical check

Base value is exact (the `p=1` Gamma integral); no numerics needed. For the general integral, a
scipy check of `S_λ(a)` vs the (later) closed form is deferred to the property/Weber units.

## GPT-5.5 Pro v1

Consult on the integrability-domination idiom + base-value reconciliation + property-(i) preview:
see `gpt56_fluctuation_defn_v1.md`.

**Consult note:** the GPT-5.5/6 reasoning model timed out (>540s) twice; per the tide "proceed
without GPT" path (standard Mathlib domination, high confidence) I filled directly and iterated with
lean-state. Both proofs landed first-attempt.

## Result

Commit on `tide/grammar-fluctuation-defn`. Theorems: `Laplace.Grammar.fluctuation` (def),
`fluctuation_integrableOn`, `fluctuation_zero`. Full `lake build Laplace` green (8879 jobs),
`scripts/sorries` clean (0/0/0/0). Surprises: none — the AM–GM domination
`nlinarith [sq_nonneg (√t - a), Real.sq_sqrt]` and the `p=1` Gamma-integral base value both went
through without iteration. `integral_rpow_mul_exp_neg_mul_rpow` (Mathlib `Integral/Gamma`) at `p=1`
is exactly `S_λ(0)=β^{-λ}Γ(λ)`.
