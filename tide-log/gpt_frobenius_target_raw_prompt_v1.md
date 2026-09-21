# Tide `frobenius-target-raw` (seabed: laplace, branch off tide/frobenius-bridge) — candidates v1

Context. The Sanity-on-Sampling note (E4) measures "the relative Frobenius error of the whole covariance against P⁻¹ and against
Σ_ULA" for ULA chains `x_{k+1} = (1 − hQ) x_k + √(2h) ξ_{k+1}` started at the mode `x_0 = 0`, `C` chains, draws `b+1..b+N`, pooled
uncentred second-moment matrix `Σ̂_raw = (1/(CN)) ∑_c ∑_k x xᵀ`. Already in the seabed (Lean 4 / Mathlib, all proved):

- `pooledSecondMoment x N b i j ω = (1/(CN)) ∑_c ∑_{k<N} x c i (b+1+k) ω * x c j (b+1+k) ω` (scalar entries, eigen-projections).
- `frobenius_pooledSecondMoment_target`: under a Gram hypothesis `E[x^c_i(k) x^{c'}_j(l)] = δ δ s₂ᵢ (ρᵢ^{|k−l|} − ρᵢ^{k+l})` and a
  FourthMomentTable, `E ∑ᵢⱼ (Σ̂ᵢⱼ − δᵢⱼ s₂ᵢ)² = E ∑ᵢⱼ (Σ̂ᵢⱼ − EΣ̂ᵢⱼ)² + ∑ᵢ (s₂ᵢ aᵢ)²`, `aᵢ = (1/N) ∑_{k<N} ρᵢ^{2(b+1+k)}`.
- `integral_pooledSecondMoment`: `E Σ̂ᵢⱼ = δᵢⱼ (1/N) ∑_{k<N} Gᵢ(b+1+k, b+1+k)`.
- `gram_realChain_dir`: the Gram table above for `realChain (ρ i) (η c · i)` with white innovations of variance `v`, `s₂ᵢ = v/(1−ρᵢ²)`.
- `inner_ulaChain_eq_realChain`: `⟨u, ulaChain Q h ξ k⟩ = realChain (1 − h p) (projNoise h u ξ) k` for an eigenvector `u` of `Q`.
- `fourthMomentTable_projNoise_dir`: the projected Gaussian noise is a FourthMomentTable with `v = 2h`.
- `frobenius_ula_le` (E4, eigenbasis) and, from the tide just finished (`frobenius-bridge`):
  `pooledRaw y N b ω : Matrix ι ι ℝ := (1/(CN)) • ∑ ∑ vecMulVec x x`; `pooledRaw_eq_conj : pooledRaw = U * Σ̂_eig * Uᵀ` pointwise
  (`U = orthoOf hQ`, `Uᵀ U = U Uᵀ = 1`); `integral_pooledRaw_apply : E Σ̂_raw = U (E Σ̂_eig) Uᵀ` entrywise;
  `sum_sq_conj : ∑ᵢⱼ (UᵀAU)ᵢⱼ² = ∑ᵢⱼ Aᵢⱼ²`; `sum_sq_diagonal`; `frobenius_ulaCov : ∑ᵢⱼ (Σ_ULA)ᵢⱼ² = ∑ᵢ (1/(pᵢ(1−hpᵢ/2)))²`;
  `frobenius_ula_le_raw` (E4 for `pooledRaw`, centred).
- `ulaCov Q h := (Q − (h/2) Q²)⁻¹`, `ulaCov_conj_eq_diagonal : Uᵀ Σ_ULA U = diag(1/(pᵢ(1 − hpᵢ/2)))` (needs `0 < h`, `hpᵢ < 2`).
- `orthoOf_transpose_inv_mul`-type lemmas: `Uᵀ Q⁻¹ U = diag(1/pᵢ)`.

Candidates.

A. `frobenius_ula_target` (eigenbasis instance of the stationary-target law for the ULA chain): with `ρᵢ = 1 − hpᵢ`, `s₂ᵢ = 2h/(1−ρᵢ²)`,
   `E ∑ᵢⱼ (Σ̂_eig,ij − δᵢⱼ s₂ᵢ)² = E ∑ᵢⱼ (Σ̂_eig,ij − EΣ̂_eig,ij)² + ∑ᵢ (s₂ᵢ aᵢ)²`, plus the closed-form mean
   `E Σ̂_eig,ij = δᵢⱼ s₂ᵢ (1 − aᵢ)` (`integral_pooledSecondMoment_ula`). Hypotheses as in `frobenius_ula_le` (`0 < h`, `hpᵢ ≤ 1`, Gaussian
   iid noise).

B. `integral_pooledRaw` (closed-form raw mean as a matrix): `E Σ̂_raw = U diag(s₂ᵢ (1 − aᵢ)) Uᵀ`, and the geometric closed form
   `aᵢ = ρᵢ^{2(b+1)} (1 − ρᵢ^{2N}) / (N (1 − ρᵢ²))` (`burnin_mean_eq`), together with `aᵢ ≤ ρᵢ^{2(b+1)}`.

C. `frobenius_ula_target_raw`: E4's MSE against `Σ_ULA` as a matrix statement,
   `E ∑ₐₐ' (Σ̂_raw − Σ_ULA)ₐₐ'² = E ∑ₐₐ' (Σ̂_raw − EΣ̂_raw)ₐₐ'² + ∑ᵢ (s₂ᵢ aᵢ)²`, via `Σ̂_raw − Σ_ULA = U (Σ̂_eig − diag s₂) Uᵀ` and
   `ulaCov_conj_eq_diagonal` (with `s₂ᵢ = 1/(pᵢ(1 − hpᵢ/2))`, equal to `2h/(1 − ρᵢ²)`). Corollary `frobenius_ula_target_raw_le`:
   `≤ [E4 envelope of frobenius_ula_le] + ∑ᵢ s₂ᵢ² ρᵢ^{4(b+1)}`.

D. `frobenius_ula_posterior_raw`: E4's MSE against the posterior covariance `Q⁻¹`,
   `E ∑ₐₐ' (Σ̂_raw − Q⁻¹)ₐₐ'² = E ∑ (Σ̂_raw − EΣ̂_raw)² + ∑ᵢ (h/(2 − hpᵢ) − s₂ᵢ aᵢ)²` — the variance plus the squared difference of the
   ULA discretisation bias `s₂ᵢ − 1/pᵢ = h/(2 − hpᵢ)` and the zero-start bias `s₂ᵢ aᵢ` (they have opposite signs: ULA inflates, zero-start
   deflates). Corollary: `≤ [envelope] + ∑ᵢ max(h/(2−hpᵢ), s₂ᵢ ρᵢ^{2(b+1)})²` or simply the two-term `(x − y)² ≤ x² + y²` when `0 ≤ x, y`
   is false in general — use `(x−y)² ≤ max(x,y)²` for `0 ≤ x,y` instead.

Numerical check (done, d=3, random PD Q, h = 0.4/p_max, N=5, b=2, C=4, 40000 Monte Carlo replicates): `Σ_ULA = U diag(s₂) Uᵀ`,
`s₂ − 1/p = h/(2−hp)` and the geometric closed form for `aᵢ` hold to 1e-16; the Monte Carlo mean of `Σ̂_raw` matches `U diag(s₂(1−a)) Uᵀ`
to within 0.4 standard errors; the two bias sums are 3.3e-3 (vs Σ_ULA) and 1.5e-3 (vs Q⁻¹) at these parameters.

Questions. (1) Are A–D correct as stated, in particular the sign/identity `s₂ᵢ(1 − aᵢ) − 1/pᵢ = h/(2 − hpᵢ) − s₂ᵢ aᵢ` and the claim that
`(x − y)² ≤ max(x, y)²` is the right two-term corollary in D? (2) Which subset is the strongest coherent single tide given the seabed
(A+B+C+D is ~300 lines by our estimate)? (3) Anything missed close to this seabed — e.g. is the relative form
`E‖Σ̂_raw − Q⁻¹‖_F² / ‖Q⁻¹‖_F²` worth stating with `frobenius_inv : ‖Q⁻¹‖_F² = ∑ 1/pᵢ²`, and does the note's "against P⁻¹" comparison
need any further term (it is computed at the same `h`, so no continuous-time target)? Please end with a vote on the subset.
