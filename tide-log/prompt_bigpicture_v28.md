You are Astra, the strategic advisor for a Lean 4 / Mathlib autoformalisation of Section 4 of the "grammar" paper (asymptotic expansions of standard integrals Z(β,n;ξ,η) = ∫_{[0,b]^d} u^h e^{-βn u^{2k} + β√n u^k ξ(u)} η(u) du in singular learning theory; thm:TaylorTree / cor:standardintegralexp). This is consult #28. Your consult #26 set the roadmap (density-first; Stage 3 = spectral truncation, never sum complete moments before a cutoff), and #27 gave the detailed Stage 3 design (units u230–u239, gates A–D). All of it is now landed, zero sorry / no additional axioms, and an independent statement-level fidelity review (v20) is being run in parallel.

## What landed since #27 (Stage 3, units 230–239)
- u230 SpectralLattice: Q = 2∏k_i, (e+1)/(2k_i) ∈ Q⁻¹ℕ_{>0}, spacing 1/Q, finite `latticeBelow Q L`.
- u231 DensityBudget (Gate A): B_Q(v) = Σ|c| j! Q^j; B_Q(stateDensityRep n w) ≤ (n+1)! Q^n for every lattice-supported w — uniform in the monomial. Also |coeffAt| j!Q^j ≤ B_Q.
- u233 MonomialRep: polynomial lists, |P(u)| ≤ ‖P‖₁ on the cube, ‖PQ‖₁ = ‖P‖₁‖Q‖₁, ‖P^p‖₁ ≤ ‖P‖₁^p, fluct.
- u234 PhaseMajorant (Gate B): M_{ν,r,p}(b) = ∫₀^∞ t^{ν-1}(1+|log t|)^r (√t)^p e^{-βt+βb√t} finite for all real b; Tonelli Σ_p (βB)^p/p! M_{ν,r,p}(b) = M_{ν,r,0}(b+B) (absolutely convergent, no smallness on B) via hasSum_integral_of_summable_integral_norm.
- u235 PhaseTaylorIdentity (Headline XXIV): Z(N) = Σ_p β^p/p! ∫ (ηJ^p) u^h g_p(N u^{2k}) exactly for every N ≥ 0 (constant bound on the box), and each phase order is a finite sum of Stage-2 monomial identities → exact polynomial Taylor tree; numerically 2e-15 in d=1.
- u236 HighSpectrumBound (Gate C): τ-side single-entry bound ∫₀¹ τ^{μ-1}(−log τ)^j g_p(Nτ) ≤ N^{-L}(1+log N)^n M_{L,n,p}(a) for μ ≥ L; |R_high(N)| ≤ K_k‖η‖₁(n+1)!Q^n M_{L,n}(ξ(0)+‖J‖₁) N^{-L}(1+log N)^n for all N ≥ 1; Z = lowSeries + R_high.
- u237 SpectralCoefficients (Gate D): regrouping by the aggregated coeffAt over latticeBelow × {0..n}, binomial reflection; A_{μ,j} = Σ_p β^p/p! K_k Σ_{(γ,c)∈ηJ^p} c Σ_{q=j}^n coeffAt(ρ_{h+γ},μ,q) C(q,j) fluctMoment_p(μ,q−j), cutoff-free, absolutely convergent; Σ_p β^p/p! mainPart_p = Σ_{μ∈Λ_L} N^{-μ} Σ_j A_{μ,j}(log N)^j exactly.
- u238 LowSpectrumTail (Headline XXV): tails summed under the absolute integral first (Tonelli on (N,∞)), e^{-βN/4} ≤ ⌈L⌉!(4/β)^⌈L⌉ N^{-L}; quantitative theorem |Z(N) − Σ_{μ∈Λ_L} N^{-μ} Σ_{j≤n} A_{μ,j}(log N)^j| ≤ C N^{-L}(1+log N)^n for all N ≥ 1, C explicit and N-free; exact form Z − Σ = R_high − tailSeries. Numerically (d=1, L=5/2) error×N^{5/2} ≈ 0.15 stable.
- u239 TaylorTreeAsymptotic (Headline XXVI): =O[atTop] N^{-L}(1+log N)^n, =O N^{-L}(log N)^n, =o N^{-L'} for L' < L.
Scope: b = 1, β > 0, k_i > 0, POLYNOMIAL ξ, η; Λ_L ⊆ Q⁻¹ℕ (coefficients vanish off the true exponent set but this is not exported); derivative dictionary β^p fluctMoment = (−∂_μ)^i ∂_a^p S_μ(a) is documented as interpretation only.

## Earlier context
Normal-block programme (Headlines VI–XXI) frozen at d65d48b with a completion statement (#25). Stage 1 (exact state density, XXII–XXII″) and Stage 2 (exact monomial moments XXIII, XXIII′) reviewed clean (v18, v19). The user's standing instruction: proceed autonomously, consult you occasionally for the big picture.

## Candidates for what to do next
(A) Stage 4 — analytic (non-polynomial) ξ, η: a coefficient space with a submultiplicative weighted ℓ¹ norm (e.g. Σ|c_γ| r^{|γ|} with r > 1 = b, from holomorphy on a polydisc of radius R > 1), evaluation/multiplication compatibility on the box, absolute summability over monomials as well as phase orders, and identification with the analytic functions — the full thm:TaylorTree hypothesis. The Stage 3 machinery is designed so that only ‖η‖₁ and ‖J‖₁ enter; the question is how much of the "list" infrastructure (MonoRep) must be replaced by summable families (e.g. ℕ^d → ℝ with finite weighted ℓ¹), and whether to route through Mathlib's `FormalMultilinearSeries`/`HasFPowerSeriesOnBall` or state the theorem for coefficient families directly (assuming Σ|c_γ| < ∞ and defining ξ as the sum).
(B) Identify Λ_L with the paper's Λ(h,k): prove spectralCoeff μ j = 0 unless μ ∈ Λ(h,k), and export the expansion over Λ(h,k) ∩ (0,L).
(C) The derivative dictionary: formalise β^p fluctMoment(μ,i,p) = (−∂_μ)^i ∂_a^p S_μ(a) (differentiation under the integral) so the coefficients read as in the paper.
(D) b ≠ 1 (general box side) by scaling.
(E) Leading-term positivity / sharpness: the minimal exponent coefficient A_{λ,m-1} is η(0)-times the Stage-1 lead coefficient times S — connect with Headlines XIII/XXI and show the expansion's first term matches the normal-block leading asymptotic.
(F) Paper-facing hand-off: mirror remark + report, then freeze Stage 3 as the deliverable ("polynomial Taylor tree") and stop.
(G) Something else you consider more valuable.

## Questions
1. Rank the candidates with go/no-go gates and unit estimates (a unit ≈ one reviewed Lean file of 150–450 lines). Which is the best next step towards the FULL thm:TaylorTree, and is Stage 4 realistically a 5–10 unit programme or a 20+ one?
2. For Stage 4: recommend the coefficient-space design concretely (types, norms, the exact hypothesis to assume on ξ, η, how to get ‖J‖-type bounds and pointwise evaluation on the closed cube, and how to interchange Σ_γ with the box integral). Should the polynomial theorem be reused by a density argument (polynomial truncations converge) or should the Stage 3 proofs be redone for summable families? Identify the single riskiest step.
3. Any statement in the Stage 3 list that you consider misleading or that should be re-stated before it is shown to the authors?
4. Where should the programme stop? Give a concrete stopping criterion.
