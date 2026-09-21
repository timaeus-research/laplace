# Tide `stepsize-tradeoff` (seabed: laplace, branch off tide/frobenius-target-raw) — candidates v1

Context. E1 of the Sanity-on-Sampling note (quadratic potentials, ULA/SGLD at relative step `h p_max` from 0.01 to 1.9) reports:
(i) "Against the plain Laplace value the stiffest direction is inflated by exactly 1/(1 − h p_max/2): a factor 2.0 at h p_max = 1, 4.0 at 1.5,
20 at 1.9"; "At κ = 1 … t⟨K⟩ = 10, 20, 100 at h p_max = 1, 1.5, 1.9 against the true 5" (d = 10).
(ii) "For the covariance as a whole the two failures trade off. For κ ≥ 100 the Frobenius error against P⁻¹ is smallest near h p_max ≈ 0.5
to 1 …, where the bias on the few stiff directions and the undersampling of the many flat ones balance. Against Σ_ULA the error simply falls
with step size, because larger steps mix faster and the discretisation is accounted for."

Seabed (all proved, Lean 4 / Mathlib). From the tide just finished (`frobenius-target-raw`): for the ULA chain from the mode with `C` chains,
draws `b+1..b+N`, `ρ = 1 − hp`, `s₂(h) = 2h/(1 − ρ²) = 1/(p(1 − hp/2))`, `zeroStartFactor ρ N b = a(h) = (1/N) ∑_{k<N} ρ^{2(b+1+k)}`
(closed form `ρ^{2(b+1)}(1 − ρ^{2N})/(N(1 − ρ²))`, `0 ≤ a ≤ ρ^{2(b+1)}`):
- `frobenius_ula_target_raw`: `E‖Σ̂ − Σ_ULA‖_F² = E‖Σ̂ − EΣ̂‖_F² + ∑ᵢ (s₂ᵢ aᵢ)²`;
- `frobenius_ula_posterior_raw`: `E‖Σ̂ − Q⁻¹‖_F² = E‖Σ̂ − EΣ̂‖_F² + ∑ᵢ (h/(2 − hpᵢ) − s₂ᵢ aᵢ)²`;
- `ula_variance_sub_inv`: `s₂ − 1/p = h/(2 − hp)`; `ula_llc`: the ULA LLC is `½ ∑ᵢ 1/(1 − hpᵢ/2)`; `ula_inflation`: `1/(1 − hp/2)`.

Candidates.

A. **Per-direction bias against Σ_ULA is antitone in the step** (`ula_bias_antitone`): for `0 < h ≤ h' ≤ 1/p`,
   `s₂(h') a(h') ≤ s₂(h) a(h)`. Proof without calculus, termwise with `u = hp ≤ u' = h'p ≤ 1`, `m = b+1+k ≥ 1`:
   `(1 − u')^{2m}(1 − u/2) ≤ (1 − u)^{2m}(1 − u'/2)` from `(1 − u')^{2m−1} ≤ (1 − u)^{2m−1}` and `(1 − u')(1 − u/2) ≤ (1 − u)(1 − u'/2)`
   (equivalent to `u ≤ u'`). Corollaries: the relative per-direction bias `(s₂ a)²/s₂² = a²` is antitone (trivial), and the bias sum
   `∑ᵢ (s₂ᵢ aᵢ)²` of `frobenius_ula_target_raw` is antitone in `h` on `(0, 1/p_max]`. This is "against Σ_ULA the error simply falls with step
   size" for the bias term (the centred term is a separate question, see Q3).

B. **Per-direction bias against Q⁻¹ changes sign, so it has an interior zero** (`posterior_bias_sign_change`, `posterior_bias_exists_zero`):
   `f(h) = h/(2 − hp) − s₂(h) a(h)` satisfies `f(h) → −1/p` as `h → 0⁺` (`a → 1`, `s₂ → 1/p`), `f(1/p) = 1/p > 0` (`ρ = 0` so `a = 0`, and
   `1/(2 − 1) · (1/p)`), and `f` is continuous on `[0, 1/p]` (rational in `h` with denominators `2 − hp ≥ 1`, `1 − hp/2 ≥ 1/2`; `a` is a
   polynomial in `h`). Hence by the intermediate value theorem `∃ h* ∈ (0, 1/p)` with `h*/(2 − h*p) = s₂(h*) a(h*)`: along that direction
   the MSE against `Q⁻¹` is pure Monte Carlo variance — the discretisation inflation exactly cancels the zero-start deflation. Also the
   explicit sign facts `f(h) < 0` for small `h` (e.g. `f(h) < 0` whenever `hp ≤ 1` and `a(h) ≥ hp/(2 − hp) · p · (1 − hp/2)`, or just the
   two endpoint values) and `f(1/p) = 1/p`. Numerically (`numcheck41.py`) the zero sits at `h*p ≈ 0.11–0.18` for `N = 7..50`, `b = 0..5`.

C. **E1 numerics** (`ula_inflation_one/…`): `1/(1 − 1/2) = 2`, `1/(1 − 1.5/2) = 4`, `1/(1 − 1.9/2) = 20`; and the isotropic LLC
   `ula_llc_isotropic`: if all `pᵢ = p` then `½ ∑ᵢ 1/(1 − hp/2) = (d/2)/(1 − hp/2)`, giving `10, 20, 100` for `d = 10` at `hp = 1, 1.5, 1.9`
   (`norm_num` instances, like `iat_flat_e1`).

Numerical check done: `s₂ a` and `a` antitone on a 400-point grid for three `(p, N, b)`; `f(0⁺) = −1/p`, `f(1/p) = 1/p` to 4 digits; the
per-term inequality holds on a grid over `u ≤ u' ≤ 1`, `m = 1..7`; the numerics of C.

Questions. (1) Are A–C correct as stated; in particular is the termwise inequality in A the right decomposition (each summand
`ρ^{2m}/(1 − hp/2)`, m ≥ 1, antitone in `h` on `[0, 1/p]`) and does antitonicity survive at `h p = 1` (`ρ = 0`)? (2) For B, is the IVT statement
the honest formalisation of "the two failures trade off … balance", and should we also state `f(h) < 0` on `(0, h*)` / `f > 0` on `(h*, 1/p)`
(monotonicity of `f`: `h/(2 − hp)` is increasing and `s₂ a` is antitone by A, so `f` is strictly increasing — is that right, giving uniqueness of
`h*`)? (3) Is there a cheap statement that the *centred* term's envelope (`∑ᵢⱼ (1 + δᵢⱼ) s₂ᵢ s₂ⱼ (1 + ρᵢρⱼ)/(1 − ρᵢρⱼ)/(CN)`, relative to
`∑ s₂ᵢ²`) also falls with `h`, or is that false (the `s₂` factors grow with `h`)? Please end with a vote on the subset A–C.
