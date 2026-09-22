# Tide `gibbs-rotation` (seabed: laplace, off tide/separable-exact) — candidates v1

Context. The Sanity-on-Sampling note's "anharm" potential is written *in a rotated frame*: `L(w) = ∑ᵢ ℓᵢ(uᵢ)`, `u = Qᵀ(w − w*)`, `Q` a random
orthogonal matrix, `ℓᵢ(x) = λᵢx²/2 + αᵢx³/6 + gᵢx⁴/24`. Tide `separable-exact` proved the exact E2 statements in the `u`-frame
(`separableAnharmonic`: `Cov_u[uᵢ, uⱼ] = δᵢⱼ Var_{ℓᵢ}`, `t(λᵢ t Var − 1) → a² − 1/2`, `t⟨wᵢ⟩ → −αᵢ/(2λᵢ²)`, `t⟨L⟩ → d/2`). The note measures
"the pooled sample covariance projected onto the eigenvectors of `P`" in the `w`-frame (the columns of `Q`), and the E7 sentence "one
direction needs only `Π_ss`" was formalised as a quadratic form along `orthoCol i`. What is missing is the **rotation law**: Gibbs moments of
`L ∘ A` for the affine isometry `A(w) = Qᵀ(w − w*)`.

Seabed (Lean 4 / Mathlib, all proved). `Laplace.Multi.partitionFunction L t = ∫ w : ι → ℝ, exp(−t L w)`, `gibbsExpectation L t φ = (∫ φ e^{−tL})/Z`,
`gibbsCov`. Change of variables `integral_comp_mulVec (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) (g) (hg : AEStronglyMeasurable g volume) :
∫ u, g u = |M.det| * ∫ v, g (M *ᵥ v)` (from `Measure.map_linearMap_addHaar_eq_smul_addHaar`); `orthoOf hP` with `Uᵀ U = U Uᵀ = 1`;
Mathlib's translation invariance of Lebesgue measure (`integral_sub_right_eq_self`, `integral_add_right_eq_self` for add-Haar measures on
`ι → ℝ`). The determinant of an orthogonal matrix: `Q.det ^ 2 = 1` from `Qᵀ Q = 1` via `det_mul`, `det_transpose`, so `|Q.det| = 1`.

Candidates.

A. **The affine-isometry law for Gibbs moments** (`partitionFunction_comp_affine`, `gibbsExpectation_comp_affine`, `gibbsCov_comp_affine`):
   for `Q` with `Qᵀ Q = 1`, `c : ι → ℝ`, and `A w := Qᵀ *ᵥ (w − c)`: `Z_{L∘A}(t) = Z_L(t)`, `⟨φ ∘ A⟩_{L∘A} = ⟨φ⟩_L`, `Cov_{L∘A}[φ∘A, ψ∘A] = Cov_L[φ, ψ]`.
   Measurability hypotheses on `φ e^{−tL}` as `integral_comp_mulVec` requires (`AEStronglyMeasurable`), or continuity of `L` and `φ`.
   Consequences for coordinates: `⟨(Q eᵢ)·(w − c)⟩_{L∘A} = ⟨uᵢ⟩_L`, `Cov_{L∘A}[(Qeᵢ)·(w − c), (Qeⱼ)·(w − c)] = Cov_L[uᵢ, uⱼ]`, and `⟨L∘A⟩_{L∘A} = ⟨L⟩_L`
   (energy invariance, so the LLC is frame-independent).

B. **E2 in the note's frame** (`rotatedAnharmonic Q c lam alpha gamma := separableAnharmonic … ∘ A`): the per-direction variance along the
   eigenvector `Q eᵢ` is the one-dimensional anharmonic variance (`gibbsCov_rotatedAnharmonic`), so the E2 remainder theorems transfer verbatim
   (`rotatedAnharmonic_var_relative_rate_note : t(λᵢ t Var_{Qeᵢ} − 1) → a² − 1/2`), the mean shift rotates (`⟨w − c⟩ = Q ⟨u⟩`, coordinatewise
   `→ −Q diag(αᵢ/(2λᵢ²))`), and `t⟨L⟩ → d/2` is unchanged. Also the Hessian of `L∘A` at `c` is `Q diag(λᵢ) Qᵀ`, so `Q eᵢ` are its eigenvectors
   with eigenvalues `λᵢ` — needed only as a remark unless the seabed's `orthoOf` should be tied to `Q` (it need not: the statement can quantify
   over any orthogonal `Q`).

C. **The one-loop covariance rotates** (`oneLoopCov_rotate`): for the rotated Taylor tensors `T'ᵢⱼₖ = ∑ Qᵢₐ Qⱼᵦ Qₖ_c T_{abc}`, `Q'` likewise,
   `oneLoopCov t (Q H Qᵀ) T' Q' = Q (oneLoopCov t H T Q₄) Qᵀ` (tide `separable-oneloop` follow-up D). Pure multilinear algebra on `Fin d`, ~150
   lines of index bookkeeping; independent of A–B.

Numerical check done (`numcheck44.py`, `d = 2`, rotated anharmonic with `θ = 0.7`, `w* = (0.3, −0.2)`, `t = 15`, quadrature): `Z` invariant
(5e-14), mean `= w* + Q ⟨u⟩` (4e-14), `Cov_w = Q Cov_u Qᵀ` (2e-13), projected variances `= Var_{uᵢ}` (2e-13), `t⟨L⟩` identical in both frames.

Questions. (1) Is A right as stated, and what is the least awkward hypothesis set — `AEStronglyMeasurable (fun w => φ w * exp(−t L w))` per use,
or continuity of `L` and `φ` once? Is there a cleaner route than `integral_comp_mulVec` + translation, e.g. `MeasurePreserving` for the affine
isometry on `ι → ℝ` (`Measure.map A volume = volume`) and `MeasurePreserving.integral_comp'`? (2) For B, is the transfer of the limit theorems
just `congr'` along `gibbsCov_rotatedAnharmonic`, or does the sign convention `αᵢ = a λᵢ^{3/2} sᵢ` need care (it is squared away in
`halpha : αᵢ² = a² λᵢ³`)? (3) Is C worth bundling, or is A+B the coherent tide with C a follow-up? Please end with a vote.
