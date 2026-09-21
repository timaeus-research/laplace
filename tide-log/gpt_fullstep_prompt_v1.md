# Context for a Lean 4 / Mathlib formalisation step (tide `fullstep-contraction`, seabed `laplace`)

Formalised so far (`Laplace/Sampler/`, Lean 4 + Mathlib pin Sep 2026): `covStep A N X = A * X * Aᵀ + N` on `Matrix ι ι ℝ`; the
spectral Lyapunov solution and its uniqueness for `A = U diag(a) Uᵀ`, `|a i| < 1`; `covStep_iterate_sub_fixed`; the ULA law
`ulaCov P h`; PSD preservation `covStep_posSemidef`; Gaussian invariance/uniqueness/convergence; the finite-chain prediction;
the ULA update as a random map.

The note *Sanity on Sampling* (E8) says that minibatch SGLD on a Gaussian target has stationary covariance solving the
*additive* Lyapunov law `Σ = AΣA + 2h I + h²t² C` (formalised, arbitrary `C`), and that including the state dependence of the
gradient noise gives the *full law*
`Σ = A Σ Aᵀ + N + c ∑_{i=1}^{n} (H_i - H) Σ (H_i - H)ᵀ`, `N = 2h I + h²t² C`, `c = h²t² (1 - m/n)/(m n)` (per-sample Hessians `H_i`,
`H = mean H_i`), which the note solves numerically by iteration for `d ≤ 50` and finds exact on linear regression. Nothing about
the full law is formalised.

Mathlib available: `ContractingWith K f` (`Topology/MetricSpace/Contracting.lean`: `ContractingWith.fixedPoint`, `fixedPoint_isFixedPt`,
`fixedPoint_unique`, `tendsto_iterate_fixedPoint`, `dist_fixedPoint_fixedPoint_of_dist_le`…), `LipschitzWith`, matrix norms as
*scoped* instances in `Analysis/Matrix.lean` (`Matrix.normedAddCommGroup` = elementwise sup norm, `Matrix.normedSpace`,
`Matrix.linftyOpNormedRing`/`linftyOpNormedAlgebra` = ∞-operator norm with `linfty_opNorm_mul : ‖A * B‖ ≤ ‖A‖ * ‖B‖`,
`linfty_opNorm_transpose`? to be checked), completeness of finite-dimensional normed spaces (`FiniteDimensional.complete`),
`Matrix.PosSemidef` (`PosSemidef.add`, `PosSemidef.smul`, `conjTranspose_mul_mul_same`), `Filter.Tendsto`, `ge_of_tendsto`.

## Candidate (Claude)

**F. The full state-dependent law as an affine contraction on matrices.** Define
`fullStep (A N : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) (c : ℝ) (X) := A * X * Aᵀ + N + c • ∑ i, D i * X * (D i)ᵀ`
(the `D i = H_i - H` are arbitrary matrices; `c ≥ 0`). Its linear part `L X := A * X * Aᵀ + c • ∑ i, D i * X * (D i)ᵀ`.
- (F1) If `L` is a contraction for some matrix norm (`LipschitzWith K L`, `K < 1`), then `fullStep` has a unique fixed point `Σ_full`,
  and the iterates from any `X₀` converge to it (`ContractingWith.fixedPoint`, `tendsto_iterate_fixedPoint`).
- (F2) A checkable sufficient condition in the ∞-operator norm: `‖A‖ ‖Aᵀ‖ + c ∑ i, ‖D i‖ ‖(D i)ᵀ‖ < 1` (from `linfty_opNorm_mul`).
- (F3) `Σ_full` is PSD when `N` is PSD and `c ≥ 0`: iterates from `0` are PSD (`covStep_posSemidef`-style) and the PSD cone is closed
  (limits of PSD matrices are PSD: pass `0 ≤ xᵀ X_n x` to the limit).
- (F4) Domination: `Σ_full ⪰ Σ_add` where `Σ_add` is the fixed point of the additive law `covStep A N` (same `A`, `N`): the iterates
  of `fullStep` from `Σ_add` are `⪰ Σ_add` and increasing, or directly `Σ_full - Σ_add = L(Σ_full - Σ_add) + c ∑ D_i Σ_add D_iᵀ` and
  the Neumann-type argument `Σ_full - Σ_add = ∑_k L^k (c ∑ D_i Σ_add D_iᵀ) ⪰ 0`; equivalently the iterates of `fullStep` from
  `Σ_add` converge to `Σ_full` and are all `⪰ Σ_add`.
- (F5) `Σ_full - Σ_add ⪰ c ∑ D_i Σ_add D_iᵀ` (first-order lower bound on the state-dependent inflation), from the same iteration.
All of F1–F5 are pure linear algebra/analysis on `Matrix ι ι ℝ`; PSD ordering is `Matrix.PosSemidef (Y - X)` (is there a `≤` on
matrices via `Matrix.instPartialOrder`/`Matrix.le_iff`? to be checked).

## Questions
1. Are F1–F5 correct as stated? In particular F4/F5: is the monotone-iteration argument right (the linear part `L` maps PSD to PSD, so
   `X ⪯ Y ⇒ L X ⪯ L Y`, and `fullStep X - covStep A N X = c ∑ D_i X D_iᵀ ⪰ 0` for PSD `X`)?
2. Which matrix norm to use for the contraction in Lean: the elementwise sup norm (`Matrix.normedAddCommGroup`, simplest instances,
   but the sufficient condition becomes ugly) or the ∞-operator norm (`Matrix.linftyOpNormedRing`, `linfty_opNorm_mul`)? How to state
   the theorem so the abstract part (F1) does not depend on the choice (e.g. take `[NormedAddCommGroup (Matrix ι ι ℝ)]`-free formulation
   via `LipschitzWith` w.r.t. a `PseudoEMetricSpace` instance passed explicitly, or fix the sup norm)? How does one obtain
   `CompleteSpace (Matrix ι ι ℝ)` under the scoped instance?
3. The PSD cone is closed: the cleanest Lean proof (`ge_of_tendsto` on `x ⬝ᵥ (X_n *ᵥ x)` with continuity of `X ↦ x ⬝ᵥ X *ᵥ x`, plus
   symmetry passes to the limit via `Continuous.matrix_transpose`)? Is there a Mathlib lemma already?
4. Is there a Loewner order on `Matrix ι ι ℝ` in the pin (`Matrix.instPartialOrder` from `StarOrderedRing`?) and lemmas like
   `Matrix.PosSemidef.le_iff`? Should F4/F5 be stated with `PosSemidef (Y - X)` directly?
5. Anything incorrect, and is F1–F5 the right size for one excursion? Better nearby target of comparable size?
Please end with a one-line vote for a single target cluster.
