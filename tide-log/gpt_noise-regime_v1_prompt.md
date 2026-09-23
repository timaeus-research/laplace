# Context: Lean formalisation of the "Sanity on Sampling" note (laplace seabed), tide 109

We are formalising, in Lean 4 + Mathlib, statements about the ULA / minibatch-SGLD sampler on the anchored Gaussian model at inverse
temperature `t`: `P_t = tH + gI`, `H = Q diag(λ) Qᵀ`, step `h`, `ρᵢ = 1 − h(tλᵢ+g)`, frame noise `Ĉ = QᵀCQ` where `C` is the gradient-noise
covariance (minibatch noise enters as `N = 2hI + h²t²C`). Tide 105 proved the long-run variance of the sampled energy `q(u) = ½uᵀHu`
under the minibatch chain's stationary Gaussian law:

  τ²_mb = ½∑ᵢⱼ λᵢλⱼ Ŝᵢⱼ² (1+ρⱼ²)/(1−ρⱼ²) + ∑ᵢⱼ λᵢλⱼ m̂ᵢ m̂ⱼ Ŝᵢⱼ (1+ρⱼ)/(1−ρⱼ),   Ŝᵢⱼ = (2hδᵢⱼ + h²t²Ĉᵢⱼ)/(1−ρᵢρⱼ),   m̂ᵢ = gŵᵢ/(tλᵢ+g).

Tide 106 took the β-scaled step `h = η/t` (`0 < ηλᵢ < 2`) and proved: (fixed C) `Ŝᵢⱼ → η²Ĉᵢⱼ/(1−(1−ηλᵢ)(1−ηλⱼ))` and `t²τ²_mb → ∞`
(when Ĉ ≠ 0); (C = C₀/t) `tŜᵢⱼ → (2ηδᵢⱼ + η²Ĉ₀ᵢⱼ)/dᵢⱼ`, `dᵢⱼ = 1−(1−ηλᵢ)(1−ηλⱼ)`, and

  t²τ²_mb → L_lin := ½∑ᵢⱼ λᵢλⱼ ((2ηδᵢⱼ + η²Ĉ₀ᵢⱼ)/dᵢⱼ)² (1+(1−ηλⱼ)²)/(ηλⱼ(2−ηλⱼ)),  with L_lin(C₀=0) = L_η := ∑ᵢ (1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)

(tide 103's exact-gradient ULA limit) and `L_η ≤ L_lin` for PSD C₀. Your earlier advice (tide 106) was to organise the batch regimes around
the scaled frame noise `tĈ_t → B`. This tide does that.

# Candidates

Write `L(B̂) := ½∑ᵢⱼ λᵢλⱼ ((2ηδᵢⱼ + η²B̂ᵢⱼ)/dᵢⱼ)² (1+(1−ηλⱼ)²)/(ηλⱼ(2−ηλⱼ))`, a function of a frame matrix `B̂` (so L(Ĉ₀) = L_lin, L(0) = L_η).

A. Scalar entry limit: if `t·c(t) → b` then `t·(2(η/t)δ + (η/t)²t²c(t))/(1−ρᵢ(t)ρⱼ(t)) → (2ηδ + η²b)/dᵢⱼ`, and the unscaled entry → 0.
B. General regime: for `C : ℝ → Matrix`, eventually PSD, with `t·(QᵀC_tQ)ᵢⱼ → B̂ᵢⱼ` for all i, j:  `t²τ²_mb(t) → L(B̂)`.
   (Proof: per-(i,j) products of A with the IAT limits `(1+ρⱼ²)/(1−ρⱼ²) → (1+(1−ηλⱼ)²)/(ηλⱼ(2−ηλⱼ))`; the mean part is
   `∑ λᵢλⱼ (tm̂ᵢ)(tm̂ⱼ) Ŝᵢⱼ (1+ρⱼ)/(1−ρⱼ)` with `Ŝᵢⱼ → 0`, `tm̂ᵢ → gŵᵢ/λᵢ`, `(1+ρⱼ)/(1−ρⱼ) → (2−ηλⱼ)/(ηλⱼ)`, so → 0.)
C. Corollaries: (C1) any `C_t` with `tĈ_t → 0` (e.g. `C₀/t²`, super-linear batch growth) gives `t²τ²_mb → L_η`; (C2) batch form `C_t = C_g/n_t`
   with `n_t/t → ν > 0` gives `t²τ²_mb → L(Ĉ_g/ν)`.
D. Strictness: for `B̂` with nonnegative diagonal, `L_η < L(B̂) ⟺ B̂ ≠ 0`. In particular `L_η < L_lin` for PSD `C₀ ≠ 0` (using `QᵀC₀Q ≠ 0`).
E. Monotonicity: if `0 ≤ B̂₁ᵢᵢ, 0 ≤ B̂₂ᵢᵢ` and `|B̂₁ᵢⱼ| ≤ |B̂₂ᵢⱼ|` for all i, j then `L(B̂₁) ≤ L(B̂₂)`; hence the C2 limit decreases as ν increases.

Regime summary we intend to write: sub-linear batch growth → `t²τ² → ∞` (tide 106), linear (`n_t ~ νt`) → finite inflation `L(Ĉ_g/ν) > L_η`,
super-linear → `L_η`.

Numerical check (d = 3, random orthogonal Q, random PSD B, D, C_g, η = 0.3, g = 0.7): `t²τ²` for `C_t = B/t + D/t^1.5` converges to L(B̂) (1e-2
relative at t = 1e4 → 1e-4 at t = 1e6); `C_t = B/t²` converges to L_η; `C_t = C_g/(νt + 5√t)` converges to L(Ĉ_g/ν); L(B̂) − L_η > 0 and
L(Ĉ_g) − L(Ĉ_g/3) > 0.

# Questions

1. Are A–E correct as stated? In particular: (i) is "eventually PSD" plus the entrywise limit `tĈ_t → B̂` the right general hypothesis, and does
   the limit B̂ inherit PSD-ness (so the nonnegative-diagonal hypothesis in D/E is automatic)? (ii) In D, is `⟺` right — could off-diagonal
   entries of B̂ cancel against the diagonal in the sum? (We think not: each (i,j) term is a square times a positive weight, so every nonzero
   entry strictly increases the sum.) (iii) In E, is the entrywise absolute-value comparison the natural monotonicity, or is there a cleaner
   order (e.g. PSD order does not obviously give entrywise |·| comparison)?
2. Which is the strongest bundle to ship in one tide, and is anything missing that is cheap given A–B (e.g. a rate `t²τ² − L(B̂) = O(1/t)` under
   `t·Ĉ_t = B̂ + O(1/t)`; a statement of the sub-linear divergence in this framework, `tĈ_t → ∞` entrywise; the mean part's exact `1/t` coefficient)?
3. How should the note phrase the regime summary in terms of batch size vs temperature — is "the long-run-variance inflation at fixed step
   ηis a function of the ratio n_t/t alone in the limit" a fair one-line reading of C2, and what caveats (Gaussian stationary law of the
   linear chain, constant-in-state noise covariance, fixed η) must accompany it?

Please give a vote: which candidates to formalise now.
