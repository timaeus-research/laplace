# Tide `direction-readings` (seabed: laplace) — candidates v1

Context. Two sentences of the Sanity-on-Sampling note about reading a covariance along an eigendirection of `P = tH` (positive definite,
eigenvalues `pᵢ`, orthonormal eigenvectors `uᵢ`, `κ = p_max/p_min`, `d` the dimension):
(E7 Design) "Along an eigenvector `s` of `P` the corrected variance is `1/p_s + Π_ss/p_s²`, so one direction needs only `Π_ss`" — for the
one-loop covariance `Cov[x] = S + SΠS`, `S = P⁻¹`.
(Summary 4) "The whole-covariance Frobenius norm hides this [a stiff-direction error] because flat directions dominate it; the LLC exposes it
because stiff directions dominate `K`."

Seabed (Lean 4 / Mathlib, all proved): `oneLoopCov t H T Q = (t•H)⁻¹ + (t•H)⁻¹ * oneLoopPi t T Q (t•H)⁻¹ * (t•H)⁻¹` on `Fin d`
(`Laplace/Multi/OneLoop.lean`); `orthoOf hP : Matrix ι ι ℝ` with `Uᵀ U = U Uᵀ = 1`, `orthoOf_transpose_mul_mul : Uᵀ P U = diag(pᵢ)`,
`orthoOf_transpose_inv_mul : Uᵀ P⁻¹ U = diag(1/pᵢ)`, `orthoCol hP i : EuclideanSpace ℝ ι` the `i`-th column with
`mulVec_orthoCol : P *ᵥ uᵢ = pᵢ • uᵢ` and `orthonormal_orthoCol`; `sum_sq_conj : ∑ᵢⱼ (UᵀAU)ᵢⱼ² = ∑ᵢⱼ Aᵢⱼ²`, `sum_sq_diagonal`,
`frobenius_inv : ∑ᵢⱼ (P⁻¹)ᵢⱼ² = ∑ᵢ (1/pᵢ)²`, `sum_mul_apply_eq_trace : ∑ᵢⱼ Aᵢⱼ Bᵢⱼ = tr(Aᵀ B)`, `trace_inv_eq_sum`; the LLC statistic of a
covariance `Σ` is `½ tr(P Σ)` (`llc_statistic_eq_weighted_diag`, `ula_llc`), equal to `d/2` at `Σ = P⁻¹`.

Candidates.

A. **E7 directional reading** (`directional_variance_eq`): for any symmetric `Π` and a unit eigenvector `s` of `P` with `P s = p s`, `p ≠ 0`,
   `sᵀ (P⁻¹ + P⁻¹ Π P⁻¹) s = 1/p + (sᵀ Π s)/p²`; instantiated for `oneLoopCov` along `orthoCol hP i`:
   `uᵢᵀ oneLoopCov uᵢ = 1/pᵢ + (uᵢᵀ Π uᵢ)/pᵢ²` with `Π = oneLoopPi t T Q (t•H)⁻¹` (no symmetry of `Π` needed for the quadratic form).
   Hypotheses: `(t•H).PosDef`. ~40 lines.

B. **Frobenius hides, the LLC exposes — the eigen-perturbation law** (`frobenius_rel_eigen_perturb`, `llc_shift_eigen_perturb`): for
   `Σ' = P⁻¹ + U diag(δ) Uᵀ`, `‖Σ' − P⁻¹‖_F²/‖P⁻¹‖_F² = ∑ᵢ δᵢ² / ∑ᵢ (1/pᵢ)²` and `½ tr(P Σ') − d/2 = ½ ∑ᵢ pᵢ δᵢ`. Then the stiff-direction case
   (`stiff_perturbation_hidden`): if `δ` is supported on the direction of `p_max` with value `δ`, the relative Frobenius error is
   `|δ|/√∑(1/pᵢ)² ≤ |δ| p_min` while the relative LLC error is `|δ| p_max/d`, so `LLC_rel ≥ (κ/d) · Frob_rel`; and the flat-direction converse
   (`flat_perturbation_dominates`): supported on `p_min`, `Frob_rel ≥ |δ| p_min/√d = √d · LLC_rel`. (Squared forms to avoid square roots:
   `LLC_rel² ≥ (κ/d)² Frob_rel²`, `Frob_rel² ≥ d · LLC_rel²`.) ~150 lines.

C. **The general two-sided comparison** (`frobenius_rel_le_llc_rel_of_stiff`): for a perturbation `δ` with `δᵢ ≥ 0` (all inflations, as
   ULA produces), `LLC_rel = ∑ pᵢδᵢ/d ≥ p_min ∑δᵢ/d` and `Frob_rel² = ∑δᵢ²/∑(1/pᵢ)² ≤ p_min² ∑δᵢ²`, so
   `Frob_rel² ≤ p_min² (∑δᵢ)² ≤ (d · LLC_rel)²` hmm — that gives `Frob_rel ≤ d · LLC_rel`, weak. The sharp statement is B's per-direction
   one; C would be: for any `δ`, `Frob_rel² ≤ p_min² ∑ δᵢ²` and `LLC_rel ≥ (1/d) ∑ pᵢ|δᵢ|` when `δ ≥ 0` — is there a clean general inequality
   worth stating, or is B the right stopping point?

Numerical check done (`numcheck42.py`, d = 6, random PD P, random symmetric Π and δ): A to 1e-12; the two identities of B to 1e-14; the
stiff case `LLC_rel/Frob_rel = 9.94 ≥ κ/d = 9.04`, the flat case `Frob_rel/LLC_rel = 5.46 ≥ √d = 2.45`.

Questions. (1) Are A and B correct as stated, including the two inequalities `∑(1/pᵢ)² ≥ 1/p_min²` (so `Frob_rel ≤ |δ| p_min`) and
`∑(1/pᵢ)² ≤ d/p_min²` (so `Frob_rel ≥ |δ| p_min/√d`)? (2) Is the "LLC" in Summary 4 correctly rendered as `½ tr(P Σ)` for a covariance `Σ`
(the note's `t⟨K⟩` at second order), so that a perturbation `δ uuᵀ` shifts it by `½ p δ`? (3) Is there a cleaner or stronger general form
for C, e.g. `Frob_rel / LLC_rel ≤ d · (weighted mean of 1/pᵢ …)`, or should the tide be A+B only? Please end with a vote.
