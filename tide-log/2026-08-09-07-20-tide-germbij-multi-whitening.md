# Tide: germbij multivariate H2b (whitening)

**Direction (user):** standing auto-mode commission on the germbij
note ("attempting to formalise these results in Lean on auto");
this tide is stage H2b of the GPT-scoped multivariate programme.
**Seabed:** laplace, branch tide/germbij-multi-gaussian at b446471
(stacked on unmerged H2a, PR #67; base main cc3c747 + H2a).
**Started:** 2026-08-09T07:20Z

## Candidates

Single candidate, fixed by the archived H2 shape consult
(tide-log/gpt56_h2_shape_v1.md in the H2a branch, rulings quoted in
the H2a tide log): for H : Matrix (Fin d) (Fin d) ℝ with hH : H.PosDef,
define qform H x := ⟪x, toEuclideanCLM H x⟫ and
K H x := exp(-qform H x / 2), and prove

1. B := toEuclideanCLM (CFC.sqrt H) has LinearMap.det ≠ 0 (via PosDef:
   Bx = 0 → ⟪x,Bx⟫ = 0 → x = 0); jac := |det|⁻¹ > 0 kept OPAQUE.
2. qform H x = ‖B x‖² (forward identity: S*S = H, mulVec_mulVec,
   B self-adjoint from (posDef_sqrt).isHermitian).
3. Change of variables: ∫ φ(Bx) = jac · ∫ φ (via
   map_linearMap_addHaar_eq_smul_addHaar hdet), integral + lintegral
   forms.
4. Z_H := ∫ K H = jac · Z₀ > 0; Integrable (K H) proven separately
   (Bochner-zero trap).
5. ∫ x_i · K H = 0; ∫ x_i x_j · K H = jac · Z₀ · H⁻¹ i j; hence
   (∫ x_i x_j K H)/(∫ K H) = H⁻¹ i j. Route: x = C y with C = B⁻¹,
   expand (Cy)_i = Σ_a C_ia y_a as finite double sum against the H2a
   delta moments (deviation from consult's riesz forms, recorded in
   the H2a log).
6. All-n polynomial integrability of (1 + ‖x‖^n)·K H by lintegral
   transport (‖Cy‖ ≤ ‖C‖‖y‖).

## Numerical check

Executed and recorded in the H2a tide log (same targets: d=2,
H=[[2,0.6],[0.6,1.1]], Z=(2π)/√det H, second moments = H⁻¹ entries
to 8 decimals). Not re-run; H2b proves exactly those identities.

## Vote

- Claude: the whitening package as staged above (consult's own plan).
- GPT-5.6 Sol: same (its H2b staging, archived verbatim).

Agreed.

## Result

Merged content (three checkpoints on this branch):

- `Laplace/Multi/QuadForm.lean`: `qform H x = ⟪x, H·x⟫`,
  `quadKernel H = exp(-qform/2)`, positivity/continuity, the
  dot-product bridge (Mathlib's `Matrix.inner_toEuclideanCLM`, free),
  `whitening H = toEuclideanCLM (CFC.sqrt H)`, sqrt PosDef + S·S = H,
  self-adjointness via the StarAlgEquiv's own `map_star'` field
  (class-level `map_star` fails to synthesize StarHomClass here),
  the forward identity `qform H x = ‖Bx‖²`, injectivity from PosDef,
  `LinearMap.det B ≠ 0` via IsUnit ker-bot + isUnit_iff_isUnit_det.
- `Laplace/Multi/QuadGaussian.lean`: opaque `jacInv H > 0`,
  `map_whitening_volume` (pushforward = ofReal jacInv • volume),
  `integral_comp_whitening` (∫ φ∘B = jacInv·∫ φ, AESM only),
  `integrable_comp_whitening`, `quadKernel_integrable`,
  `quadKernel_integrable_pow` (all n, operator-norm domination
  ‖x‖ ≤ ‖C‖·‖Bx‖), `integral_quadKernel` (Z_H = jacInv·(2π)^{d/2}),
  positivity.
- `Laplace/Multi/QuadMoments.lean`: `whiteningInv` (matrix
  nonsing-inverse route, C∘B = id via nonsing_inv_mul),
  coordinate expansion (Cy)_i = Σ_a S⁻¹_{ia} y_a, the two
  finite-sum contraction lemmas against the H2a delta moments,
  `integral_coord_mul_quadKernel` (M1 = 0),
  `integral_coord_mul_coord_quadKernel`
  (M2 = jacInv·Z₀·H⁻¹_{ij}, Gram step S⁻¹(S⁻¹)ᵀ = (S·S)⁻¹ = H⁻¹),
  `normalized_second_moment_quadKernel` (M2/Z = H⁻¹_{ij}: the
  Jacobian and Z₀ cancel exactly as the consult predicted).

Stage H2 — the consult-flagged "largest API spike" of the
multivariate programme — is complete across the two tides.

Surprises:

1. The whole whitening layer had exactly TWO genuinely new error
   classes: (a) class-level `map_star` cannot synthesize
   StarHomClass for `Matrix.toEuclideanCLM`'s ≃⋆ₐ type — use the
   structure field `.map_star'` directly; (b) a `rfl` bridging
   `(CLM S * CLM S) x` to a def-wrapped composition hits a whnf
   heartbeat timeout — rewrite with `ContinuousLinearMap.mul_apply`
   and fold via a `have hcomp` equation instead.
2. `open scoped MatrixOrder` is required in EVERY file touching
   CFC.sqrt on matrices (the partial order instance is scoped);
   errors surface as baffling PartialOrder synthesis failures at
   each use site.
3. The deviation from the consult (coordinate double-sum expansion
   instead of riesz linear-functional forms) cost ~60 lines of
   Finset contraction and needed nothing new — the fallback was
   never needed.
