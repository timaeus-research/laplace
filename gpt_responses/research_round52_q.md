# Research consult, round 52: what is still missing from the map of responses?

Same seabed (rounds 50–51 on file). Since round 51, ALL formalised sorry-free:

* Full-simplex mixture path: `KL(rν‖ν) = ∫₀¹(1−s)k`, `KL(ν‖rν) = ∫₀¹ s k`, `∫₀¹ k = symmetrised KL`
  (bounded positive density).
* Entropy-Taylor engine: `q_t = 1 + tg + O_{L^∞}(t²)` a.e. ⇒ `(∫ klFun q_t)/t² → ½∫g²`.
* Lift = conditional expectation of the density; tilt density `p_t = 1 + th + O(t²)` uniformly; the four
  quadratic limits `‖h‖²/2`, `‖B₀h‖²/2`, fibre `∫(h−g)²/2`, marginal `(∫g² − ⟨a,u⟩)/2` with `g = E_ν[h|σ(S)]`:
  the quadratic shadow of `KL = 𝓘 + R + L` is complete.
* Atlas refinement for an affine coarse-graining `S = TS' + b`: coarse family ⊆ fine family, a family member is its own
  projection, `KL(D‖Π_S) = KL(D‖Π_{S'}) + KL(Π_{S'}‖Π_S)`, `𝓘_{S'} = 𝓘_S + KL(Π_{S'}‖Π_S)`; observational tower already
  existed.
* The one-line map: `KL(D‖ν) = ∫₀¹(1−s)κ + L + R` for every finite-information `D` (boundary included) and along the
  bridge `KL(D_s‖ν) = ∫₀ˢ(s−u)κ + L_s + R_s`.
* Cramér upper/lower bounds for the empirical response under the featureless member were already in the seabed
  (`cramer_upper`, `cramer_lower`).

Remaining from your round-51 list: (4) the `L¹`-valued derivative of the reconstruction density `Dq(m)[u] = q_m ℓ_{m,u}`
and the mixed Hessian; (5) the conditional variational formula `L = sup_g E_D[g − log E_ν(e^g|σ(S))]`.

The user's programme: "map the space of responses across the data manifold, from the featureless distribution of
maximal entropy to the actual data distribution, with maximum beauty and depth".

## Questions

1. Looking at the whole edifice now, what is the single most valuable *structural* theorem still missing — something
   that would make a reader say the map is complete? Candidates: (i) the reconstruction `D ↦ Π(M_D)` as a differentiable
   retraction of the (finite-information) laws onto the exponential family, with differential the `L²` projection `B`
   (an infinitesimal version of the retraction: for a bounded score `h` at a reconstructed law `Q_M`, the derivative
   of `t ↦ Π(M_{Q_M e^{th}})` is `Q_M · B_M h`); (ii) the dually-flat picture: the two affine structures (mean and
   natural coordinates) on the atlas with the Bregman divergence as canonical divergence, and the generalised
   Pythagorean theorem for e-/m-geodesics (we have KL(Q_A‖Q_C) = KL(Q_A‖Q_B) + KL(Q_B‖Q_C) + ⟨A−B, q(B)−q(C)⟩; is the
   orthogonality statement — the mixed term vanishes iff the m-geodesic A→B is orthogonal to the e-geodesic B→C in
   the Fisher metric at B — worth formalising as the geometric heart?); (iii) the Fisher metric on the response space
   as a varying inner product `g_M(u,z) = ⟨u, Σ_M⁻¹ z⟩` with its two dual connections, and the statement that the
   atlas path (m-geodesic) and the exponential path (e-geodesic) are the two geodesics of the dual connections;
   (iv) the interpretation of `κ` as `g_{M_s}(v,v)` (already true by definition) plus the "length" `∫√κ` vs energy
   `∫κ` inequality (Cauchy–Schwarz) and the exact relation of `KL` to the Fisher–Rao length? (v) something else.
2. For the conditional variational formula (5) and the `L¹` derivative (4): give the precise minimal statements and the
   cheapest Lean routes given the seabed (bounded tests, clipped log-ratio; `Measure.tilted` differentiation in `L¹`),
   with the pitfalls; and say honestly whether either is worth doing before (1).
3. Are there *exact identities* we have not written down that follow immediately from what exists — e.g. the
   second-order expansion of the observable defect `Δ_φ(s)` at `s = 0` (we have `Δ'_φ(0) = E_D(I−B₀)φ − E_ν(I−B₀)φ`
   and the atlas `F''`), a mixture-compensation identity along the bridge for the three terms simultaneously,
   the Pythagorean identity for the *reverse* divergence `KL(ν‖D)`, or an "area formula" `KL(D‖ν) − KL(ν‖D) =` something
   along the atlas path? Please list the ones you consider elegant with proof sketches.
4. Rank everything (≤ 400 Lean lines each) by depth × feasibility.
