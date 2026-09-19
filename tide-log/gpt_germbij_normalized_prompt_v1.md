# Tide deliberation: germbij, normalized singular identifiability (Lean 4 + Mathlib, laplace seabed)

You are helping pick and vet a formalisation target. Context: the note "What expectation values know about the loss landscape" (Elliott–Murfet, 2026; codename germbij) studies the map Φ_L : φ ↦ asymptotic expansion of ⟨φ⟩_t = ∫φ e^{-tL} / ∫ e^{-tL} as t → ∞, for L ≥ 0 real analytic near a compact zero locus W₀ = {L = 0} ⊆ ℝ^d, φ ∈ C_c^∞. Already proven in the note AND formalised in Lean (repo timaeus-research/laplace):

- thm:singular (unnormalized): if ∫φ e^{-tL₁} − ∫φ e^{-tL₂} = o(t^{-∞}) for every φ ∈ C_c^∞, with L₁, L₂ ≥ 0 analytic at each point of W₀ and vanishing on W₀, then L₁ = L₂ on a neighbourhood of W₀. Proof: pencil identity e^{-tL₁} − e^{-tL₂} = t∫₀¹ g e^{-tL_s} ds with g = L₂ − L₁, observable φ = gψ, and the sector lower bound.
- lem:sector: K ≥ 0 C² near p with K(p) = 0, a real analytic near p with nonzero germ, ψ ∈ C_c^∞, ψ ≥ 0, ψ ≡ 1 near p ⇒ ∫ a² ψ e^{-tK} ≥ C t^{-N} for large t (N ≥ m + d/2, m the vanishing order of a).
- prop:one-point: the normalized version follows wherever W₀ has a point with ratio-based constructive recovery.

The note's remaining open question was q:proportional: do there exist L₁ ≠ L₂ (nonneg analytic, common compact zero locus) whose unnormalized families are exactly proportional, ∫φ e^{-tL₂} ≃ C(t) ∫φ e^{-tL₁} for all φ ∈ C_c^∞, for some scalar series C(t) ≢ 1? (Φ_{L₁} = Φ_{L₂} is equivalent to this with C = Z₂/Z₁.)

On 2026-08-26 a co-author inserted the following proof into the note directly under the Question (verbatim, lightly reformatted):

> No. Indeed, take φ smooth with compact support inside W, take y = w_i a coordinate, and use integration by parts:
>   ∫ ∂φ/∂y e^{-tL} dw = t ∫ φ ∂L/∂y e^{-tL} dw.
> Taking ∂φ/∂y and φ ∂L₁/∂y as observables, we obtain from the assumption that
>   ∫ φ ∂L₂/∂y e^{-tL₂} ≃ C(t) ∫ φ ∂L₁/∂y e^{-tL₁};   ∫ φ ∂L₁/∂y e^{-tL₂} ≃ C(t) ∫ φ ∂L₁/∂y e^{-tL₁}.
> Subtracting and setting L = L₁ − L₂: ∫ φ ∂L/∂y e^{-tL₂} dw = o(t^{-∞}) for all φ ∈ C_c^∞(W).
> Replace φ by φ ∂L/∂y with φ ≥ 0, φ ≡ 1 near a zero p of L₂. Applying lem:sector, ∂L/∂y has zero germ at p. Since this is true for all directions y, L (analytic) must be constant. Since L₁ and L₂ have a common nonempty zero set, this constant must be 0.

This is not yet a theorem environment, has no Lean counterpart, and the surrounding prose still says the question is open. Note that ≃ here means equality of asymptotic expansions, i.e. difference o(t^{-∞}); the first displayed ≃ is the hypothesis applied to ∂φ/∂y after dividing both sides by t, which is harmless for o(t^{-∞}).

## Lean seabed (what exists)

- `SuperPoly f := ∀ N : ℕ, f =o[atTop] fun t ↦ t^(-(N:ℝ))`.
- `pencil_families_force_eq_near_smooth {ι} [Fintype ι] {L₁ L₂ : (ι → ℝ) → ℝ} {W₀} (hL1c : Continuous L₁) (hL2c) (hL1 : ∀ w, 0 ≤ L₁ w) (hL2) (hA1 : ∀ p ∈ W₀, AnalyticAt ℝ L₁ p) (hA2) (hzero1 : ∀ p ∈ W₀, L₁ p = 0) (hzero2) (hfam : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ N, (fun t ↦ ∫ w, φ w * (exp(-(t*L₁ w)) - exp(-(t*L₂ w)))) =o[atTop] t^(-N)) : ∃ U, IsOpen U ∧ W₀ ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w`, plus the point form `∀ᶠ w in 𝓝 p, L₁ w = L₂ w`.
- `sector_lower_bound_multi (K a) (m) … : (volume S).toReal * (c² e^{-4C0} t^{-m - d/2}) ≤ ∫ w in (√t)⁻¹ • S, a w ^2 * exp(-(t*K w))` — general in K, a; `leading_part_scaled_set`, `analytic_remainder_bound`, `quadratic_upper_bound_of_nonneg` (C² K ≥ 0 near 0, K 0 = 0 ⇒ K ≤ C0‖w‖² on a ball), `exists_least_nonzero_diagonal` (HasFPowerSeriesOnBall g p 0 r, g 0 = 0, g not identically zero on the ball ⇒ least m with a nonzero diagonal `p m (fun _ ↦ x₀) ≠ 0`, ‖x₀‖ = 3/2), `exists_bump_one_on_ball`, `contDiff_mul_of_tsupport_subset`.
- `one_point_anchoring_contradiction`: already takes the projective hypothesis in the form `SuperPoly (fun t ↦ ∫ φ e^{-tL₂} − C t * ∫ φ e^{-tL₁})` with an arbitrary `C : ℝ → ℝ`.
- Mathlib: `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable {f g : E → 𝕜} {v : E} (hf'g : Integrable (fun x ↦ fderiv ℝ f x v * g x) μ) (hfg' : Integrable (fun x ↦ f x * fderiv ℝ g x v) μ) (hfg : Integrable (fun x ↦ f x * g x) μ) (hf : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x) (hg : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x) : ∫ x, f x * fderiv ℝ g x v ∂μ = - ∫ x, fderiv ℝ f x v * g x ∂μ`; `is_const_of_fderiv_eq_zero`, `IsOpen.is_const_of_fderiv_eq_zero`, `Convex.eqOn_of_fderivWithin_eq`; `AnalyticAt.fderiv`; `ContDiff.continuous_fderiv`.

Cross-seabed facts (the user asked us to consider them): the hironaka repo (Lean v4.33.1) has discharged statements `exists_logResolutionData_of_analyticOnNhd` (chart form for |K| at a zero of an analytic K on an open U ⊆ ℝ^d: finitely many charts with two-sided monomial bounds on |K|∘φ and the Jacobian, transport certificates, covering a neighbourhood up to a null set) and `exists_hasLLCExponentsOn_of_analyticOnNhd_nonneg` (∃ λ ∈ ℚ_{>0}, θ ∈ {1..d}: volume{K ≤ ε} ∩ cube =Θ[ε→0⁺] ε^λ(−log ε)^{θ−1} for all small cubes). The greybook repo (v4.33.1, depends on hironaka) has `hasPreciseLaplace_of_hasPreciseRLCT_general`: precise sublevel asymptotics C ε^λ (−log ε)^m ⇒ ∫ e^{-nK} ~ C Γ(λ+1) n^{-λ} (log n)^m (precise constants only, no Θ version). laplace is on Lean v4.33.0 with no dependency on either; using them means a toolchain bump and two new lake dependencies.

## Candidates

**A. Normalized singular identifiability theorem (formalise the inserted proof).**
```
theorem normalized_families_force_germ_eq_at {ι} [Fintype ι] {L₁ L₂ : (ι → ℝ) → ℝ} {p : ι → ℝ}
  (h1 : ContDiff ℝ ∞ L₁) (h2 : ContDiff ℝ ∞ L₂) (hL1 : ∀ w, 0 ≤ L₁ w) (hL2 : ∀ w, 0 ≤ L₂ w)
  (hA1 : AnalyticAt ℝ L₁ p) (hA2 : AnalyticAt ℝ L₂ p) (hp1 : L₁ p = 0) (hp2 : L₂ p = 0)
  {C : ℝ → ℝ}
  (hfam : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
     SuperPoly (fun t ↦ (∫ w, φ w * exp (-(t * L₂ w))) - C t * ∫ w, φ w * exp (-(t * L₁ w)))) :
  ∀ᶠ w in 𝓝 p, L₁ w = L₂ w
```
and the locus form `∃ U, IsOpen U ∧ W₀ ⊆ U ∧ ∀ w ∈ U, L₁ w = L₂ w` under `∀ p ∈ W₀` hypotheses, as in the pencil theorem. Proof plan: (i) IBP lemma `∫ (fderiv φ w v) e^{-tL} = t ∫ φ (fderiv L w v) e^{-tL}` for smooth compactly supported φ and C¹ L (Mathlib lemma with f = φ, g = e^{-tL}; integrability from compact support and continuity). (ii) Apply hfam to ∂_vφ and to φ·∂_vL₁ (smooth compactly supported since L₁ is C^∞); multiply the second by t and subtract to cancel C: `SuperPoly (fun t ↦ ∫ φ (∂_v(L₂−L₁)) e^{-tL₂})` (using that t·SuperPoly is SuperPoly). (iii) Take φ := ψ · ∂_v(L₂−L₁) with ψ a smooth bump ≡ 1 near p supported in the analyticity ball; get `SuperPoly (∫ ψ (∂_v g)² e^{-tL₂})`. (iv) If the germ of ∂_v g at p is nonzero, the sector lower bound with a = ∂_v g (analytic at p by AnalyticAt.fderiv) and K = L₂ (C², ≥ 0, L₂ p = 0 ⇒ quadratic upper bound) gives ≥ κ t^{-N}, contradiction; hence ∂_v g = 0 eventually near p for every coordinate direction v, so fderiv g = 0 on a ball, g constant on the ball, g p = 0 ⇒ g = 0 near p. (v) Assembly over W₀ as in `pencil_families_force_eq_near`.

**B. Forward direction at a singular point by cross-seabed bridge.** For analytic K ≥ 0 on open U, K w = 0, not identically zero near w: ∃ λ ∈ ℚ_{>0}, θ: ∫_{cube} e^{-tK} =Θ[atTop] t^{-λ}(log t)^{θ−1}, from hironaka E5 plus a Θ-Abelian transfer (to be written; greybook's is precise-constant only). Requires the laplace toolchain bump and dependencies. We view this as the next arc rather than this tide.

**C. Equal zero loci are forced, projective form (companion to A).** Under the smoothness/nonnegativity hypotheses of A and the projective hypothesis, if L₁ p = 0 but L₂ p ≠ 0 for some p while L₂ vanishes somewhere, contradiction: a bump ψ at p gives ∫ψ e^{-tL₁} ≳ t^{-d/2} (quadratic upper bound) while ∫ψ e^{-tL₂} = O(e^{-δt}), so C(t) = o(t^{-∞}); then every ∫φ e^{-tL₂} is o(t^{-∞}), contradicting a bump at a zero of L₂.

## Questions

1. Is the inserted proof (candidate A) correct as written? Please check in particular: (a) that lem:sector applies with K = L₂ (only C² and ≥ 0 with L₂(p) = 0 are needed) and a = ∂_y(L₁ − L₂); (b) the step from "∂_y L has zero germ at p for every coordinate y" to "L is constant near p", and what regularity/connectedness is used; (c) whether the argument needs L₁ ∈ C^∞ (so that φ ∂_yL₁ is an admissible observable) or whether analyticity near W₀ alone suffices given the observable class C_c^∞(W); (d) whether the scalar C(t) needs any property (positivity, being a power-log series) or whether an arbitrary function C : ℝ → ℝ works, as our Lean statement assumes; (e) whether the conclusion should be stated for W₀ = common zero set or can be weakened as in C.
2. Which candidate is the strongest single tide we can reasonably reach with the seabed above? Do you agree A is the right target and B the follow-up?
3. Are there better or additional targets close to this seabed that we missed — in particular, anything the hironaka/greybook statements unlock cheaply for germbij (e.g. a Θ-Abelian transfer as its own lemma, a chart-form corollary about the exponents of the expansion), or a sharper formulation of A (e.g. quantitative: which N and κ)?

Please end with a one-line vote: which single candidate you back for this tide.
