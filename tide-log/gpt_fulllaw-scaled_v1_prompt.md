# Context: laplace seabed, tide 116 (E8 at the anchored scaling)

Tide 115 formalised the first-order lower bound `LLC_full ≥ LLC^{mb} + (t/2)c∑ⱼλⱼ(B̂(Σ^{mb}))ⱼⱼ/(1−ρⱼ²)` for the E8 full law (`B(X) = ∑ᵢDᵢXDᵢᵀ`,
`ρⱼ = 1−hpⱼ`, `pⱼ = tλⱼ+g`, frame `Q`). Tide 101: `LLC^{mb} = (t/2)∑λⱼ(1 + ht²Ĉⱼⱼ/2)/(pⱼκⱼ)`, `LLC^{ULA} = (t/2)∑λⱼ/(pⱼκⱼ)`, `κⱼ = 1−hpⱼ/2`. Tide 106:
at `h = η/t` with fixed `C`, `(QᵀΣ^{mb}Q)ₖₗ → η²Ĉₖₗ/(1−αₖαₗ)`, `αⱼ = 1−ηλⱼ`.

# Candidates (fixed C, D, c; h = η/t)
A. `Σ^{mb}(t) → Σ∞ := QŜ∞Qᵀ`, `Ŝ∞ₖₗ = η²Ĉₖₗ/(1−αₖαₗ)` (matrix limit from the entry limits).
B. `(1/t)·(t/2)c∑ⱼλⱼ(B̂(Σ^{mb}(t)))ⱼⱼ/(1−ρⱼ²) → σ₁ = ½c∑ⱼλⱼ(QᵀB(Σ∞)Q)ⱼⱼ/(ηλⱼ(2−ηλⱼ))` (continuity of `Σ ↦ (QᵀB(Σ)Q)ⱼⱼ`).
C. `(1/t)(LLC^{mb} − LLC^{ULA}) → σ_mb = (η/4)∑ⱼĈⱼⱼ/(1−ηλⱼ/2)`.
D. `(1/t)(LLC^{mb} + first-order term − LLC^{ULA}) → σ_mb + σ₁`.
Numerical check (3D): σ₁ = 0.01594, σ_mb = 0.2764; `corr₁/t` = 0.0232, 0.0168, 0.01603, 0.01595 at t = 10…10⁴; `(LLC^{mb}−LLC^{ULA})/t` → 0.27636.

# Questions
1. Are A–D correct as stated (in particular that `c` is `t`-independent at this scaling and that `B̂(Σ^{mb})ⱼⱼ` has a finite nonzero limit, so the
   Hessian-fluctuation correction is genuinely `Θ(t)` like the constant-noise inflation, contradicting nothing in tides 107/114 where `1−L = Θ(h)`
   was the concern — the resolvent factor `1/(1−ρⱼ²) → 1/(ηλⱼ(2−ηλⱼ))` is `O(1)` at this scaling, not `O(1/h)`; please reconcile)?
2. Is the ratio `σ₁/σ_mb` a useful diagnostic for the note ("when does the Hessian fluctuation matter relative to the gradient-noise inflation")?
   Any simplification of `σ₁` when `Dᵢ` commute with `H` (per-sample Hessians sharing the eigenframe): `(QᵀB(Σ∞)Q)ⱼⱼ = ∑ᵢ d̂ᵢⱼ²Ŝ∞ⱼⱼ` so
   `σ₁ = ½c∑ⱼλⱼ(∑ᵢd̂ᵢⱼ²)η²Ĉⱼⱼ/((1−αⱼ²)²)`?
3. Wording for E8 Summary 2 ("the LLC is inflated by about h t² tr(C_g)/(2d), which at fixed relative step grows linearly in t"): should the
   note add that the Hessian-fluctuation correction grows linearly too, with slope σ₁?
Vote please.
