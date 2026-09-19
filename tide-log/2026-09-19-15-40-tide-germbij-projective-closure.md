# Tide: germbij projective identifiability closure

**Direction (user):** "Ok let's continue with the formalisation and exploration of this … statements involving actual expectation values (i.e. with the 1/Z incorporated) …" — continued on auto; this tide takes the two stretch corollaries recorded by the normalized-singular tide (equal zero loci in projective form; the scalar `C(t) = 1 + o(t^{-∞})`).
**Seabed:** laplace, commit a52c51b (main; NormalizedSingular + SufficientFamilies merged)
**Started:** 2026-09-19T15:40Z
**Ledger direction:** germbij: projective (normalized) identifiability closure — equal zero loci forced and the scalar C(t) = 1 + o(t^-infty), via a Gaussian-type lower bound of the localized Laplace integral near a zero.

## Seabed snapshot

- `normalized_families_force_germ_eq_at/_eq_near` (NormalizedSingular): projective SuperPoly agreement over
  `C_c^∞` ⇒ `L₁ = L₂` near common zeros; `normalized_expectations_force_eq_near` (1/Z form with window χ).
- `sector_lower_bound_multi` (Sector): `vol(S)·c²·e^{-4C₀}·t^{-m-d/2} ≤ ∫_{t^{-1/2}S} a² e^{-tK}` given
  `K ≤ C₀‖w‖²` on a ball and `|a(t^{-1/2}x)| ≥ c t^{-m/2}` on `S`. With `a ≡ 1`, `m = 0` this is the
  Gaussian-type lower bound `∫ e^{-tK} ≳ t^{-d/2}` — assembled once already inside
  `analytic_square_weight_eq_zero_near`, not yet as a standalone lemma.
- `quadratic_upper_bound_of_nonneg` (SingularPrep): `C²`, `K(0)=0`, `K ≥ 0` near 0 ⇒ `K ≤ C₀‖w‖²` on a ball.
- `exists_bump_one_on_ball` (SingularPrep); `laplace_moment_bounded`, `anchor_moment_eq` (OnePointAnchoring):
  `|∫φ e^{-tL}| ≤ ∫|φ|` for `t ≥ 0`, exact equality of anchor moments on a region where `L₁ = L₂`.
- `superPoly_of_mul_anchor`, `superPoly_sub_of_scalar_gauge`, `anchored_proportionality_remove_scalar`
  (Anchoring): the scalar-gauge algebra, all conditional on a polynomial lower bound `hanchor_low`
  which the seabed never discharges. `lower_bound_not_superpolynomial` (Decay).
- Missing: (i) a standalone Gaussian-type lower bound near a zero; (ii) exponential smallness of
  `∫ψ e^{-tL}` when `L ≥ δ > 0` on `supp ψ`; (iii) the polynomial bound `|C(t)| = O(t^{d/2})`; (iv) the
  equal-zero-loci theorem; (v) `SuperPoly (C − 1)` and the transfer projective ⇒ exact.
