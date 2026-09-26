# Round 60: the three complementary statements are in place — final architecture and what is missing (germbij / laplace)

Same programme and conventions as rounds 52–59. User direction unchanged: "map the space of responses across the
data manifold, from the featureless distribution of maximal entropy to the actual data distribution, with maximum
beauty and depth."

## Landed since round 59 (all sorry-free on `main`; slop paragraphs pushed)

Your order was: (1) global entropy-graph reconstruction theorem with an actual `L¹`/TV estimate, (2) `L¹`-differential
retraction, (3) refinement/residual tower as one package, (4) all-orders after a smoothness prototype. Landed:

- (1) `EntropyGapTotalVariation`: `(∫|r_A − r_B| dν)² ≤ (2/(ab))[a𝓘(A) + b𝓘(B) − 𝓘(aA+bB)]` with `r = dΠ/dν`
  (Radon–Nikodym densities, whole finite-rate domain; sign test), and TV continuity of `Π` on the finite-rate
  domain for the `(M, 𝓘(M))` topology along any filter (`tendsto_integral_abs_rnDeriv_sub_of_tendsto_genRate`).
- (2) `DifferentialRetraction`: `reconstructionL1 M = [q_M] ∈ L¹(ν)` (via `Integrable.toL1`),
  `reconstructionDeriv M : 𝕍 →L L¹` (`u ↦ [q_M ℓ_{M,u}]`, `LinearMap.toContinuousLinearMap`),
  `HasFDerivAt (fun z ↦ reconstructionL1 (M+z)) (reconstructionDeriv M) 0` at every interior `M`;
  `H(q_M ℓ_{M,u}) = u`; `P_M(q_M g) = q_M B_M g` for bounded centred `g`; idempotence. NOT yet: continuity of
  `M ↦ reconstructionDeriv M` (`C¹`), `C²`.
- (3) `RefinementTower`: `refinement_tower` = the two base splits + `KL(D‖Π_c) = KL(D‖Π_f) + KL(Π_f‖Π_c)` +
  `𝓘_f = 𝓘_c + KL(Π_f‖Π_c)` (the identities were already in `AtlasRefinement`).
- Also `DualCurveComparison` (mixture vs exponential curve, `−B(ℓ²)`, pairing `−Eℓ³`), `SegmentStability`,
  `ObservableTaylorUniform`, `EmpiricalTotalVariation` (from round 58).

Mathlib constraints (this pin): no CLT; no Banach analytic IFT; smooth IFT `ContDiffAt.to_localInverse` exists;
`contDiff_succ_iff_fderiv` exists.

## Questions

1. Final architecture. The note now has: (A) interior response geometry (scores, normal Hessian, compact-uniform
   relative Peano, observable Taylor, dual-flat, dual curves); (B) dependence on the data law (retraction,
   `L¹`-differential with regression tangent map, TV-Lipschitz on compacts, empirical consistency); (C) radial
   transport (accounting identity, TV ≤ Fisher speed, information budget at every finite-rate response); (D)
   boundary completion (radial) and global entropy-gap stability (non-radial); (E) information resolution
   (refinement tower, fibre/marginal split). Write the ONE-PARAGRAPH theorem statement you would put at the top of
   the note (in words + the five displayed identities), and list any statement you consider essential that is
   still missing or mis-stated. In particular: is "the reconstruction is continuous on the finite-rate domain for
   the `(M, 𝓘(M))` topology" the right way to say it, or should it be stated as a Lipschitz-type modulus in the
   Jensen gap (which we have)? Is there a converse (TV convergence of reconstructions ⇒ `𝓘` converges)? — I think
   yes by lower semicontinuity + `KL(Π(M_*)‖Π(M_i))`-type bounds; give the precise statement if it is clean.
2. `C¹` of `reconstructionL1`: I plan `‖Dp_M − Dp_{M'}‖_{op} ≤ K₂ Λ · ∫|q_M − q_{M'}| + sup_x |ℓ_{M,u} − ℓ_{M',u}|`
   with the second term `≤ |J|((‖M‖+B)‖R_M − R_{M'}‖ + ‖R_{M'}‖‖M − M'‖)`, both → 0 as `M' → M` in `ri K` by
   continuity of `R` and TV-Lipschitz. Any pitfall, and is `C¹` worth stating before `C²` (which would need
   the polarised Hessian `q N(ℓ_uℓ_w)` as an `L¹`-valued second derivative — we have the pointwise formula and the
   compact-uniform relative Peano, which gives the diagonal `L¹` second-order expansion; the mixed formula would
   follow by polarisation once `C²` is known)?
3. All-orders prototype: the cheapest concrete first step? Options: (a) `ContDiff ℝ ⊤ (fun θ ↦ ∫ φ dP_θ)` by
   induction with `contDiff_succ_iff_fderiv` (derivative field of the same form), (b) `iteratedDeriv` along a line
   `t ↦ q_{M+tu}(x)` with the recursion, (c) the linewise moment-normality statement. Which single lemma would you
   prototype first to gauge the cost?
4. Anything else that would raise the beauty/depth of the map at low cost (e.g. the converse in 1, a "Fisher–Rao
   length ≥ TV" statement, the `L²(Q)`-orthogonality of the tangent projection as an explicit inner-product
   identity, the empirical second-order stochastic response without CLT (an `o_p(1/n)` statement is not available
   without rates; but `E‖M̂_n − M‖² = tr Γ/n` IS available with bounded features — is
   `E[ E_{Π(M̂_n)}F ] = E_{Π(M)}F + ½ Σ Γ_ij b_F[e_i,e_j]/n + o(1/n)` reachable with only second moments + the
   compact-uniform Peano + a tail bound (Hoeffding/Chebyshev) on the event that `M̂_n` leaves the neighbourhood?
   Give the sketch and cost if so — that would be the "reconstruction bias" theorem.)
