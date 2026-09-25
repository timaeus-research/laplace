# Context: tide 117 of an automated Lean formalisation run (laplace seabed, Sanity-on-Sampling note)

Previous tides established, for the discrete-time linear-response "full law" of an SGLD-type sampler with Hessian-fluctuation noise,
X = A X Aᵀ + N + c·B(X), B(X) = ∑ᵢ Dᵢ X Dᵢᵀ, A = I − hP = U diag(1 − hpᵢ) Uᵀ, N = minibatchNoise h t C = 2h·I + h²t²·C:
- (tide 107) a unique fixed point `fullFixed` exists when fullLipschitz := ‖A‖‖Aᵀ‖ + c∑‖Dᵢ‖‖Dᵢᵀ‖ < 1 (ℓ∞ operator norm), and Σ_full ⪰ Σ^{mb} = R(N) (R = Lyapunov resolvent);
- (tide 115) Δ = Σ_full − Σ^{mb} = c·R(B(Σ_full)) exactly; Δ ⪰ cR(B(Σ^{mb})); in the frame tr(H R(Y)) = ∑ λᵢ Ŷᵢᵢ/(1−ρᵢ²);
- (tide 116) at the anchored scaling h = η/t, pᵢ = tλᵢ + g with C, Dᵢ, c fixed: Σ^{mb}(t) → Σ∞ = QŜ∞Qᵀ with Ŝ∞ₖₗ = η²Ĉₖₗ/(1−αₖαₗ), αⱼ = 1 − ηλⱼ; the first-order term has slope σ₁ = ½c∑ⱼλⱼ(QᵀB(Σ∞)Q)ⱼⱼ/(1−αⱼ²); the constant-noise inflation LLC^{mb} − LLC^{ULA} has slope σ_mb = (η/4)∑Ĉⱼⱼ/(1−ηλⱼ/2). You (GPT) remarked that when the Dᵢ share the eigenframe, the full slope is ∑ⱼwⱼ/(1−qⱼ) and the first-order diagnostic understates it near qⱼ = 1.

# Candidates v1 for this tide (commuting eigenframe: Dᵢ = U diag(dᵢ) Uᵀ)

Notation: N̂ = UᵀNU, vⱼ = ∑ᵢ dᵢⱼ², sⱼ = 1 − αⱼ² = ηλⱼ(2−ηλⱼ), qⱼ = c vⱼ/sⱼ, wⱼ = ½λⱼη²Ĉⱼⱼ/sⱼ = ηĈⱼⱼ/(2(2−ηλⱼ)).

A. Exact full law. In the frame (Uᵀ(AXAᵀ)U)ₖₗ = aₖaₗX̂ₖₗ and (UᵀB(X)U)ₖₗ = (∑ᵢdᵢₖdᵢₗ)X̂ₖₗ, so the full law is entrywise:
   Σ̂ₖₗ = N̂ₖₗ/(1 − aₖaₗ − c∑ᵢdᵢₖdᵢₗ). Define frameFullFixed U a c d N := U·[that matrix]·Uᵀ. Claim: it is a fixed point of the full step whenever all denominators are nonzero, and equals `fullFixed` when additionally fullLipschitz < 1.
B. LLC: tr(H·frameFullFixed) = ∑ⱼλⱼN̂ⱼⱼ/(1 − aⱼ² − cvⱼ); with minibatch noise (t/2)tr(HΣ_full) = (t/2)∑ⱼλⱼ(2h + h²t²Ĉⱼⱼ)/(1 − (1−hpⱼ)² − cvⱼ).
C. Anchored scaling (qⱼ < 1 for all j): (LLC_full − LLC^{ULA})/t → σ_full = ½∑ⱼλⱼη²Ĉⱼⱼ/(sⱼ − cvⱼ) = ∑ⱼwⱼ/(1−qⱼ), where LLC^{ULA} = (t/2)∑ⱼλⱼ/(pⱼ(1−hpⱼ/2)) = (t/2)∑ⱼλⱼ·2h/(1−ρⱼ²). Per mode the two `2h` pieces contribute O(1) and the η²Ĉⱼⱼ piece Θ(t).
D. σ₁ in the frame: (UᵀB(Σ∞)U)ⱼⱼ = vⱼŜ∞ⱼⱼ, so σ₁ = ½c∑ⱼλⱼvⱼη²Ĉⱼⱼ/sⱼ² = ∑ⱼwⱼqⱼ, σ_mb = ∑ⱼwⱼ, hence σ_mb + σ₁ = ∑ⱼwⱼ(1+qⱼ) ≤ ∑ⱼwⱼ/(1−qⱼ) = σ_full with exact deficit ∑ⱼwⱼqⱼ²/(1−qⱼ) (for 0 ≤ qⱼ < 1, wⱼ ≥ 0).

Numerical check (d = 3, n = 2, η = 0.3, g = 0.5, c = 0.05, random Q, C ⪰ 0, dᵢ): closed form is a fixed point to 1e−16 and matches the iterated step; fullLipschitz = 0.925 at t = 10³; σ_full = 0.536421, σ_mb + σ₁ = 0.532009, deficit 0.004412 exact; (LLC_full − LLC^{ULA})/t → 0.536421 with O(1/t) approach.

# Questions
1. Are A–D correct as stated? In particular: (i) is the entrywise reduction right for the off-diagonal entries (the denominator 1 − aₖaₗ − c∑ᵢdᵢₖdᵢₗ), and what is the cleanest sufficient condition for all denominators to be nonzero/positive — does |a| < 1 plus qⱼ < 1 for all j imply it via Cauchy–Schwarz (c|∑ᵢdᵢₖdᵢₗ| ≤ c√(vₖvₗ) < √(sₖsₗ) ≤ 1 − aₖaₗ ?), or is a separate hypothesis needed? (ii) Is the identification with `fullFixed` under the ℓ∞ contraction hypothesis the right way to state uniqueness, or should we state uniqueness of the entrywise solution directly (it is unique whenever all denominators are nonzero, without any norm condition)?
2. Is the slope σ_full = ∑wⱼ/(1−qⱼ) the "full slope" you had in mind in tide 116, and is the statement "the first-order diagnostic σ_mb + σ₁ understates the exact slope by ∑wⱼqⱼ²/(1−qⱼ)" the right way to phrase the E8 point? Should we also record the ratio σ_full/σ_mb = ∑wⱼ/(1−qⱼ)/∑wⱼ as the exact version of R₁?
3. Which is the strongest reachable bundle for one tide (A–D is ~250 Lean lines on top of the existing frame lemmas), and are there better or additional candidates close to this seabed (e.g. the stability threshold qⱼ → 1 as the blow-up of the full law in the commuting case; the non-commuting case via a Schur-product bound)?
4. Wording against the note's E8 for a staged `\leanref` proposal (one paragraph), with the caveats you would insist on.
Please end with a one-line vote (which candidates to formalise).
