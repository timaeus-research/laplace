# Research consult, round 34 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI: "core features of the change in posterior expectation values with the change in the data
distribution; map the space of responses across the data manifold, from the featureless distribution of maximal
entropy to the actual data distribution; maximum beauty and depth"). All formal, sorry-free, on `main`.

## Landed since round 33 (your ranking: 1 boundary, 2 N^⊥, 3 two-axis integrability, 4 three-point, 5 Cramér,
## 6 second-order loss surface, 7 lengths, 8 walls)

1. Boundary rays — COMPLETE. `FaceLimit`: tilt `q_λ ∝ e^{−λV}π`, `V` bounded, essential lower bound `α`, face
   `F = {V = α}`: `e^{λα}Z_λ → ∫_F π`; if `∫_F π > 0`: `⟨φ⟩_λ → (∫_F φπ)/(∫_F π)` for every bounded `φ`,
   `λ⟨V−α⟩_λ → 0`, `KL(q_λ‖π̄) → −log π̄(F)`; instantiated on the feature ray `a = sv` (tilt of `e^{−tL₀}π` by `R_v`).
   `FaceInfinite`: `KL(q_λ‖π̄) = E_{q_λ}[log r]`, two-event tangent bound `KL ≥ q_λ(A) log(q_λ(A)/π̄(A)) − 1`,
   concentration `q_λ({V < α+ε}ᶜ) ≤ e^{−λε/2} Z₀/π̄(A_{ε/2})`, `π̄(A_ε) → π̄(F)`, hence `KL → +∞` when `π̄(F) = 0`
   (with `π̄(A_ε) > 0` for all `ε`).
2. `N^⊥` — DONE by restriction (`EffectiveFeatures`): no nondegeneracy; `P_{a+n} = P_a` for `n ∈ N`; `ker C = N`;
   for any complement `W` of `N`: `m|_W : W ≃ range m` (bijective), `G > 0` on `W`, `dim W + dim N = |ι|`.
3. Two-axis integrability — DONE (`TwoAxisResponse`): along data lines, mixed partials of `⟨φ⟩` in both orders equal
   `−Cov(φ,D) + t κ₃(φ,D,L_s)`; of `A = log Z` equal `−⟨D⟩ + t Cov(D,L_s)`.
4. Three-point identity — was already landed (`mixKL_three_point`, `mixKL_pythagoras`).
Earlier this session: constrained responses (single/multi), slice chart + loss surface + reduced potential (block
Hessian), annealing ray (`E' = −Var`, `∫Var = E(0)−E(T)`, `KL(P_T‖π̄) = ∫₀ᵀ u Var_u ≤ T(E(0)−E(T))`, observable
change bound), data mixtures (`L_ν` affine in `ν`), third cumulant / Amari–Chentsov tensor, featureless point.

Not done: 5 Cramér (large deviations of the empirical response — no LDP machinery in Mathlib; feasible only as the
Chernoff upper bound?), 6 second-order loss surface (blocked on differentiability of the regression coefficients
`b(t,M) = C⁻¹c` along the temperature path: `C_t⁻¹` needs matrix-inverse differentiability, or your envelope trick
`σ²(t) = min_{b'} Var_t(L₀ − b'·R)` — but the envelope theorem needs a priori differentiability of the min), 7 lengths,
8 walls.

## Questions
1. **Audit** the boundary theorems and `EffectiveFeatures` as stated. In `FaceInfinite` the zero-mass hypothesis is
   `∫_{V=α} π = 0` together with `∀ ε > 0, ∫_{V<α+ε} π > 0`; is the second automatic from `α` being the essential
   infimum (yes, by definition — but our `hα : ∀ᵐ x, α ≤ V x` alone does not force it; fine?).
2. **Re-rank what remains and propose new directions** for the PI's goal now that rounds 29–33 are essentially
   closed. Candidates: (i) the second-order loss surface — give the cleanest route around `C⁻¹` differentiability
   (e.g. differentiate the identity `C_t b_t = c_t` along the path using only that `C_t` is invertible and the
   derivative of `C_t` and `c_t` exist: then `ḃ = C⁻¹(ċ − Ċ b)` — is `b` differentiable a priori? via the implicit
   function theorem on `(t, b) ↦ C_t b − c_t`, or by writing `b_t = adj(C_t) c_t / det C_t` (Cramer) which is a
   polynomial in differentiable entries — the Cramer route needs no inverse differentiability at all!); (ii) a
   Chernoff/exponential-tightness statement `P_{t,0}^{⊗n}(R̄_n ∈ closed set away from m(0)) ≤ e^{−n inf ℐ}`
   as the formalisable half of Cramér; (iii) thermodynamic length bounds `(∫₀ᵀ √Var_u)² ≤ T(E(0) − E(T))` and the
   Fisher-length lower bound on observable change (cheap); (iv) the global "journey" theorem: the path
   `(t, a) : [0,1] → ` joint chart from `(0, ·)` (prior) to `(t*, a*)` (data), with total information
   `KL(P_data ‖ π̄)` decomposed as `∫` of the response form along the path (path-independent Bregman
   integral?) — is there an exact statement like `KL(P_{θ₁}‖P_{θ₀}) = ∫₀¹ (1−s) G_{θ_s}(θ̇,θ̇) ds` for the natural
   segment (we have the affine-line version at fixed t; the joint natural segment is `natKL_zero_eq_integral`);
   (v) the "moment body of the data manifold": the image of the space of data distributions `{ν}` under
   `ν ↦ (L_ν)` and then under the response map — the set of responses reachable by changing the data alone at fixed
   temperature is all of `int K` (already: `range_meanMap_slice`) — but reachable by *actual* data distributions
   (mixtures of a finite family of losses `ℓ(·, z)`)? (vi) anything else core.
3. For your top pick give the Lean-friendly formulation and pitfalls.
