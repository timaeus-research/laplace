# Tide `rosenbrock-terminating` (laplace seabed, main 94c6d10): candidates for GPT-6 Astra

## Context

E5 of the note: Rosenbrock `L(x, y) = (a (y − x²)² + (1 − x)²)/2` in `d = 2`, minimiser `(1, 1)`, "the `w₂` integral is
Gaussian given `w₁`, so exact moments are one-dimensional quadratures and the exact LLC is `d/2 = 1` at *every* `t`"; E7: "the
valley is exactly a parabola, so the series terminates: the stiff variance is `1/(500t) + 2/(5t²)` and nothing else". The seabed
has the exact Rosenbrock moments via the triangular shear `z = x − 1 ~ N(0, 1/t)`, `u = y − x² ~ N(0, 1/(at))` independent
(`gibbsExpectation_rosenbrock_fst = 1`, `_snd = 1 + 1/t`, `_self = 1/t`, `rosenCov_eq_laplace_add`: `Cov = (tH)⁻¹ + (2/t²) e_y e_yᵀ`),
the tensors `rosenHess = [[1+4a, −2a], [−2a, a]]`, `rosenT` (`T₀₀₀ = 12a`, `T₀₀₁ = T₀₁₀ = T₁₀₀ = −2a`), `rosenQ` (`Q₀₀₀₀ = 12a`),
`(tH)⁻¹ = (1/t) rosenSigma`, `rosenSigma = [[1, 2], [2, 4 + 1/a]]`, `contractT_rosenbrock = (4a/t, −2a/t)`, `bubble_rosenbrock`,
`contractQ_rosenbrock`, and `oneLoopCov_rosenbrock` (the one-loop covariance is exact). Since this morning: `twoLoopEnergy t H T Q4 :=
½ tr(HS) + (t/12) θ + (t/8) δ − (1/8) q` (theta `∑ᵢⱼ Sᵢⱼ (TSST)ᵢⱼ`, dumbbell `(T:S)ᵀ S (T:S)`, figure-eight `∑ (Q4:S)ᵢⱼ Sᵢⱼ`),
`meanShift t H T := −½ S (t T:S)`, `covKFormula t H T B b := ½ tr(HSBS) + ½ (Sb)⬝(T:S) − (t/2) b⬝(SHS (T:S)) − (t/2) (Sb)⬝(T:(SHS))`.
The Rosenbrock polynomial machinery: `gibbsExpectation_rosenbrock_of_poly (c : Fin 5 → Fin 5 → ℝ)` evaluates
`⟨∑ᵢⱼ cᵢⱼ zⁱ uʲ⟩ = ∑ cᵢⱼ mᵢ(1) mⱼ(a)` with the harmonic moment vector `![1, 0, 1/(λt), 0, 3/(λt)²]`, from the general
`gibbsExpectation_harmonic_pow_even/odd`.

## Candidates (symbolically verified, `numcheck_rosenbrock_terminating.py`)

**A. The two-loop energy is exact for Rosenbrock.** `θ = 12a/t³`, `δ = 4a/t³`, `q = 12a/t²`, so
`(t/12)θ + (t/8)δ − q/8 = (a + a/2 − 3a/2)/t² = 0` and `twoLoopEnergy t rosenHess rosenT rosenQ = ½ tr(HS) = 1/t =
⟨L⟩` at every `t > 0` (`twoLoopEnergy_rosenbrock`, `twoLoopEnergy_rosenbrock_exact`). Note `θ = 3δ`: a non-separable check of the
weights `1/12`, `1/8`, `−1/8` (this morning's separable family only sees `1/12 + 1/8`).

**B. eq:mean is exact for Rosenbrock.** `meanShift t rosenHess rosenT = (0, 1/t) = (⟨x⟩ − 1, ⟨y⟩ − 1)` (`meanShift_rosenbrock`,
`meanShift_rosenbrock_exact`).

**C. eq:covK for Rosenbrock misses exactly `3B₂₂/t³`.** For the probe `ψ = ½ vᵀBv + b⬝v`, `v = (x − 1, y − 1)`:
`covKFormula t rosenHess rosenT B b = (a B₀₀ + 2a(B₀₁ + B₁₀) + (4a + 1) B₁₁ + 2a b₁)/(2a t²)` and the exact
`Cov[L, ψ] = covKFormula + 3 B₁₁/t³` (`gibbsCov_rosenbrock_probe`); in particular eq:covK is *exact for linear probes* (`B = 0`):
`Cov[L, b⬝v] = b₁/t²`. The remainder is `Cov[z²/2, ½B₁₁ (z²)²] = B₁₁ (⟨z⁶⟩ − ⟨z²⟩⟨z⁴⟩)/4 = 3B₁₁/t³`: the flat direction's
`z²` term of `y − 1 = u + 2z + z²`, i.e. the same valley-curvature mechanism as the `2/t²` in `Var y`. Lean: `L·ψ` has `z`-degree 6,
so the moment vector must be extended to `Fin 7` (`⟨z⁵⟩ = 0`, `⟨z⁶⟩ = 15/(λt)³`) with a `Fin 7 → Fin 5` version of the polynomial
evaluation; `⟨ψ⟩` fits the existing `Fin 5 → Fin 5`.

## Questions

1. Are A, B, C correct as stated (in particular the sign conventions of `covKFormula`, whose last two terms reduce to `−½ (Sb)⬝(T:S)`
   each because `SHS = S/t`, so `covKFormula = ½ tr(HSBS) − ½ (Sb)⬝(T:S)`)? Is "the series terminates" the right reading of A and B
   given that `⟨L⟩ = 1/t` and `⟨w⟩ − w* = (0, 1/t)` exactly?
2. C shows the first-order eq:covK is *not* exact for Rosenbrock even though the one-loop covariance and the two-loop energy are.
   Is the `3B₂₂/t³` remainder what the two-loop (second-order) eq:covK would produce, i.e. would the second-order `Cov[K, ψ]` also
   terminate? (Not for this tide; for the staging note's wording.)
3. Lean: generalising `gibbsExpectation_valley_poly` from `Fin 5 → Fin 5` to `Fin n → Fin m` is a copy of the proof; is there a
   pitfall in stating `harmonicMoment_vec7` with `![1, 0, 1/(λt), 0, 3/(λt)², 0, 15/(λt)³]` and using `Fin.sum_univ_seven` in the
   coefficient identity `L(p)·ψ(p) = ∑ᵢⱼ cᵢⱼ (p.1 − 1)ⁱ (p.2 − p.1²)ʲ` (35 symbolic coefficients in `a, B, b`, closed by `ring`)?
4. Scope and vote (A+B+C)?
