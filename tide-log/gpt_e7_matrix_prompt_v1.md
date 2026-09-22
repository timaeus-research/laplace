# Tide `e7-matrix` (laplace seabed, commit a5fdc8f): candidates for GPT-6 Astra

## Context

The Sanity-on-Sampling note's E7 measures, for E2's rotated `d`-dimensional anharmonic oscillator, the relative Frobenius error of the
exact covariance against the Laplace covariance `(tH)⁻¹` and against the one-loop-corrected covariance, and finds `O(1/t)` vs `O(1/t²)`.
The seabed now has every ingredient in scalar / eigenframe form; this tide should state E7 in the note's own matrix terms.

Seabed (Lean 4 + Mathlib; `ι` a `Fintype`, `Q : Matrix ι ι ℝ` with `Qᵀ * Q = 1`, `A(w) = Qᵀ(w − c)`,
`rotatedAnharmonic Q c lam alpha gamma = separableAnharmonic lam alpha gamma ∘ affineFrame Q c`, `separableAnharmonic lam alpha gamma u =
∑ᵢ ℓᵢ(uᵢ)`, `ℓᵢ(x) = λᵢx²/2 + αᵢx³/6 + γᵢx⁴/24`):

```lean
-- Laplace/Multi/OneLoop.lean (indices are `Fin d`)
noncomputable def contractQ (Q : Fin d → Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑ k, ∑ l, Q i j k l * S k l
noncomputable def contractT (T : Fin d → Fin d → Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : Fin d → ℝ :=
  fun l => ∑ m, ∑ n, T l m n * S m n
noncomputable def bubble (T) (S) : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => ∑ k, ∑ l, ∑ m, ∑ n, T i k l * S k m * S l n * T j m n
noncomputable def tadpoleLine (T) (S) : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => ∑ k, ∑ l, T i j k * S k l * contractT T S l
noncomputable def oneLoopPi (t : ℝ) (T) (Q) (S) : Matrix (Fin d) (Fin d) ℝ :=
  (-(t / 2)) • contractQ Q S + (t ^ 2 / 2) • bubble T S + (t ^ 2 / 2) • tadpoleLine T S
noncomputable def oneLoopCov (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (T) (Q) : Matrix (Fin d) (Fin d) ℝ :=
  (t • H)⁻¹ + (t • H)⁻¹ * oneLoopPi t T Q (t • H)⁻¹ * (t • H)⁻¹
theorem oneLoopCov_oneDim … : oneLoopCov t !![lam] (fun _ _ _ => alpha) (fun _ _ _ _ => gamma) = !![1/(lam*t) + (alpha²/lam⁴ − gamma/(2 lam³))/t²]
-- Laplace/Multi/AmbientMoments.lean
theorem gibbsCovMatrix_rotatedAnharmonic (hQ : Qᵀ * Q = 1) (c) (hlam) (hgamma) (hdisc) (ht : 0 < t) :
    Matrix.of (fun j k => gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) (fun w => w k)) =
      Q * diagonal (fun i => gibbsCov (separableAnharmonic lam alpha gamma) t (fun u => u i) (fun u => u i)) * Qᵀ
theorem frobenius_rel_laplace_rotatedAnharmonic (hQ) (c) {a} (hlam) (hgamma : ∀ i, gamma i = lam i ^ 2) (halpha : ∀ i, alpha i ^ 2 = a ^ 2 * lam i ^ 3) (ha : a ^ 2 < 3) :
    Tendsto (fun t => t ^ 2 * ((∑ j, ∑ k, (Cov_w t j k - (Q * diagonal (fun i => 1 / (lam i * t)) * Qᵀ) j k) ^ 2) /
        ∑ j, ∑ k, (Q * diagonal (fun i => 1 / (lam i * t)) * Qᵀ) j k ^ 2)) atTop (𝓝 ((a ^ 2 - 1 / 2) ^ 2))
-- Laplace/Multi/VarianceOrder3.lean (this morning)
theorem var_anharmonic_order2_rate_sharp (hlam) (hgamma) (hdisc) : ∃ K T, 0 ≤ K ∧ 1 ≤ T ∧ ∀ {t}, T ≤ t →
    |t * Var_t[x] - 1 / lam - (alpha ^ 2 / lam ^ 4 - gamma / (2 * lam ^ 3)) / t| ≤ K / t ^ 2      -- one-dimensional ℓ
theorem separableAnharmonic_var_order2_rate_note_sharp … (i : ι) : … |t * (lam i * t * gibbsCov (sepAnh) t (fun w => w i) (fun w => w i) - 1) - (a ^ 2 - 1 / 2)| ≤ K / t
-- Laplace/Sampler/FrobeniusBridge.lean
theorem sum_sq_conj (A U : Matrix ι ι ℝ) (hUU' : U * Uᵀ = 1) : ∑ i, ∑ j, (Uᵀ * A * U) i j ^ 2 = ∑ i, ∑ j, A i j ^ 2
theorem sum_sq_diagonal (d : ι → ℝ) : ∑ i, ∑ j, (diagonal d) i j ^ 2 = ∑ i, d i ^ 2
-- Laplace/Sampler/FrobeniusTarget.lean: inv_eq_conj_diagonal — `(Q diag p Qᵀ)⁻¹ = Q diag(1/p) Qᵀ` for `QᵀQ = 1`, `p ≠ 0`
-- Laplace/Multi/SeparableExact.lean: gibbsCov_separableAnharmonic … : gibbsCov (sepAnh) t (fun u => u i) (fun u => u j) = if i = j then Var_i else 0
```

## Candidates

**A. `oneLoopCov` on the rotated tensors, in closed form.** With `ι = Fin d`, `H := Q * diagonal lam * Qᵀ`,
`rotT Q alpha i j k := ∑ l, alpha l * Q i l * Q j l * Q k l`, `rotQ Q gamma i j k m := ∑ l, gamma l * Q i l * Q j l * Q k l * Q m l`
(these are the third and fourth derivative tensors of `L∘A` at its minimum `c`; we do not prove that, we take them as data), and
`S = (t • H)⁻¹ = Q diag(1/(λt)) Qᵀ`:
`contractQ (rotQ Q gamma) S = Q diag(γᵢ/(λᵢt)) Qᵀ`, `contractT (rotT Q alpha) S = fun l => ∑ p, α_p Q l p /(λ_p t)`,
`bubble (rotT Q alpha) S = Q diag(αᵢ²/(λᵢt)²) Qᵀ`, `tadpoleLine (rotT Q alpha) S = Q diag(αᵢ²/(λᵢt)²) Qᵀ`,
hence `oneLoopPi = Q diag(αᵢ²/λᵢ² − γᵢ/(2λᵢ)) Qᵀ` and
`oneLoopCov t H (rotT Q alpha) (rotQ Q gamma) = Q * diagonal (fun i => 1/(lam i * t) + (alpha i ^ 2/lam i ^ 4 − gamma i/(2 lam i ^ 3))/t ^ 2) * Qᵀ`.
Key factorisation for the quadruple sums: `∑ₖₘ Q k p * S k m * Q m q = (Qᵀ S Q) p q = δ_pq/(λ_p t)`, so
`bubble i j = ∑ p q, α_p α_q Q i p Q j q ((QᵀSQ) p q)²` and `tadpoleLine i j = ∑ p, α_p Q i p Q j p ∑ q, α_q (QᵀSQ) p q (QᵀSQ) q q`.

**B. E7, matrix form.** For the rotated oscillator with `Cov_w(t) j k := gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t (fun w => w j) (fun w => w k)`:
`∃ K T, 0 ≤ K ∧ 1 ≤ T ∧ ∀ t ≥ T, (∑ j k, (Cov_w t j k − oneLoopCov t H (rotT Q alpha) (rotQ Q gamma) j k)²) / (∑ j k, ((t • H)⁻¹ j k)²) ≤ K / t⁴`
(relative squared Frobenius error `O(t⁻⁴)`, i.e. relative RMS `O(t⁻²)`). Proof: `Cov_w = Q diag(Varᵢ) Qᵀ`, A, `sum_sq_conj`,
`sum_sq_diagonal`, and per coordinate `|Varᵢ − 1/(λᵢt) − Cᵢ/t²| ≤ Kᵢ/t³` from `var_anharmonic_order2_rate_sharp` divided by `t`;
denominator `∑ᵢ 1/(λᵢt)² = (∑ 1/λᵢ²)/t²`.

**C. The contrast.** In the note's parametrisation (`γᵢ = λᵢ²`, `αᵢ² = a²λᵢ³`), `Cᵢ = (a² − ½)/λᵢ²`, and the seabed's
`frobenius_rel_laplace_rotatedAnharmonic` gives `t² · rel²(Laplace) → (a² − ½)²`. Package: `∃ K T, ∀ t ≥ T, rel²(oneLoop) ≤ K/t⁴`, and
if `a² ≠ ½` then `∃ c > 0, T, ∀ t ≥ T, rel²(Laplace) ≥ c/t²` (from the limit). Both relative to `‖(tH)⁻¹‖_F` (also state with `oneLoopCov`
written in the note's form `S + SΠS`, which is its definition).

## Numerical check (`numcheck_e7_matrix.py`, `d = 3`, `λ = (1, 2, 5)`, `a = ½`, random orthogonal `Q`)

`‖oneLoopCov − Q diag(1/(λt) + C/t²) Qᵀ‖_F = 1.7e-16` at `t = 7`, with `contractQ`, `bubble`, `tadpoleLine` each matching their closed forms
to `1e-16`; `t²‖Cov − oneLoopCov‖_F/‖S‖_F = 0.206, 0.238, 0.255, 0.264, 0.269` at `t = 20 … 320` (bounded), while
`t‖Cov − S‖_F/‖S‖_F = 0.260, 0.256, 0.253, 0.252, 0.251 → 0.25 = |a² − ½|`.

## Questions

1. Are the closed forms in A correct, including `bubble = tadpoleLine` and the signs in `Π` (`−(t/2)·γ/(λt) + (t²/2)·2·α²/(λt)² = α²/λ² − γ/(2λ)`)?
   Is the identification of `rotT`, `rotQ` with the derivative tensors of `L∘A` at `c` right (so that the statement is E7 for E2's setup)?
2. Lean strategy for the quadruple sums: is the `(QᵀSQ)_{pq}` factorisation the right idiom (rewrite each contraction as a sum over the
   eigen-indices using `Finset.sum_comm`/`Finset.mul_sum`, then `Matrix.mul_apply` for `(QᵀSQ) p q`, then `diagonal_apply` and
   `Finset.sum_ite_eq`), or is there a slicker route (e.g. prove `bubble T S = Q * diagonal (…) * Qᵀ` by `ext` and a single
   `simp [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]` + `Finset.sum_comm` normal form)? Any Mathlib lemma for
   `∑ k, Q k p * Q k q = if p = q then 1 else 0` from `Qᵀ * Q = 1` (we have `congrFun (congrFun hQ p) q` with `Matrix.mul_apply`)?
3. B: is the statement with the squared relative error and `K/t⁴` the right normal form, or should the headline be
   `√(∑(Cov − oneLoop)²)/√(∑ S²) ≤ K/t²` (needs `Real.sqrt` bookkeeping)? Should the denominator be `‖S‖_F` (as the note) or `‖Cov‖_F`?
4. Scope and vote: A+B+C as one tide? Anything to sharpen or correct?
