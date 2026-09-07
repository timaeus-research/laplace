/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.LeadingCoeffPositive

/-!
# Headline statements of the grammar §4 formalisation (d = 2, one chart)

Thin, paper-facing wrappers around the main theorems of `Laplace/Grammar`, with the hypotheses
spelled out and the chart integral identified with the paper's standard integral. Nothing is
re-proved here. Scope (to be read with every statement below):

* dimension `d = 2`, one resolution chart, box `[0, b]²`, phase `u^{k₁} v^{k₂}` with exponents
  `(h₁, h₂)`, `(k₁, k₂)`; the standard integral is evaluated at `√n = N`;
* the phase `ξ` and amplitude `η` are given by their Taylor data `x, y : ℕ × ℕ → ℝ`, absolutely
  summable at a radius `ρ > b` (`WSummable ρ`): `ξ(u,v) = ∑ x_{ij} u^i v^j`, `η = ∑ y_{ij} u^i v^j`;
* the canonical coefficients `A_α, B_α` are those of units 121–124 (cutoff-independent).

NOT claimed: general `d`; the multi-chart / resolution assembly; the functional CLT for the
empirical process; the identification of the paper's `C^ω` topology with the weighted coefficient
norm; convergence of expectations from convergence in distribution beyond the stated domination
hypotheses; a full posterior-ratio expansion. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology Asymptotics

namespace Laplace.Grammar

/-! ### The standard integral -/

/-- **The chart integral is the paper's standard integral** (defn:std_integral at `√n = N`):
`Z(β, N²; ξ, η) = ∫∫_{(0,b]²} u^{h₁} v^{h₂} e^{−β(N u^{k₁}v^{k₂})²} η(u,v)
  e^{β N u^{k₁}v^{k₂} ξ(u,v)}`,
with `ξ = dblSum x`, `η = dblSum y`. -/
theorem headline_standard_integral (β b ρ N : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hb : 0 < b) (hbρ : b < ρ)
    (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x) (hy : WSummable ρ y) :
    twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
      = ∫ u in Ioc (0 : ℝ) b, u ^ h₁ * ∫ v in Ioc (0 : ℝ) b, v ^ h₂
          * (Real.exp (-β * (N * (u ^ k₁ * v ^ k₂)) ^ 2)
            * (dblSum y u v * Real.exp (β * (N * (u ^ k₁ * v ^ k₂)) * dblSum x u v))) := by
  unfold twoDAmp
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
  congr 2
  exact anaAmp_ampCoeff β b ρ hb hbρ x y hx hy u v _ (Ioc_subset_Icc_self hu)
    (Ioc_subset_Icc_self hv)

/-! ### The Taylor tree (thm:TaylorTree, d = 2) -/

/-- **thm:TaylorTree for `d = 2`, all `(h, k)`**: for every truncation `T`,
`Z(N) = ∑_{α ∈ Λ(h,k), α < 2T} N^{−α} (A_α log N + B_α) + O(N^{−2T}(1 + log N))`. The exponent set
`polesBelowGen` is `Λ(h,k) ∩ (−∞, 2T)` with `Λ(h,k)` the union of the two arithmetic progressions
`(h_i+1)/k_i + ℕ/k_i` (in the `√n`-normalisation). -/
theorem headline_taylor_tree (β b p₁ p₂ ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (x y : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (hy : WSummable ρ y) (T : ℝ) :
    (fun N : ℝ => twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (ampCoeff β x y) b)
        - ∑ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
            N ^ (-α) * (canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) α * Real.log N
              + canonB β b h₁ h₂ k₁ k₂ (anaFaceU (ampCoeff β x y) b) (anaFaceV (ampCoeff β x y) b)
                  (fun i j s => ampCoeff β x y (i, j) s) α))
      =O[atTop] fun N : ℝ => N ^ (-(2 * T)) * (1 + Real.log N) :=
  twoD_taylor_tree_general β b p₁ p₂ ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ x y hx hy T

/-- **Uniform remainder on bounded analytic families** (a refinement not stated in the paper): for
Taylor data in the ball `‖a‖ ≤ M` of the coefficient-pair space and every `N ≥ 1`, the remainder is
at most `K(β,b,ρ,M,h,k,T) N^{−2T}(1 + log N)` with `K` independent of the data. -/
theorem headline_taylor_tree_uniform (β b p₁ p₂ ρ : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (M : ℝ) (hM : 0 ≤ M) (a : CoeffPair) (ha : ‖a‖ ≤ M)
    (T N : ℝ) (hN : 1 ≤ N) :
    |chartZ β b ρ h₁ h₂ k₁ k₂ N a
        - ∑ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
            N ^ (-α) * (coeffA β ρ h₁ h₂ k₁ k₂ α a * Real.log N + coeffB β b ρ h₁ h₂ k₁ k₂ α a)|
      ≤ uniformTreeConst β b ρ M (2 * M) p₁ p₂ T h₁ h₂ k₁ k₂ 0
        * (N ^ (-(2 * T)) * (1 + Real.log N)) :=
  chartZ_taylor_tree_ball β b p₁ p₂ ρ h₁ h₂ k₁ k₂ hβ hb hbρ hk₁ hk₂ hp₁ hp₂ M hM a ha T N hN

/-- **The leading coefficient** for equal starting exponents `p = (h₁+1)/k₁ = (h₂+1)/k₂`:
`A_p = y₀₀/(k₁k₂) ∫₀^∞ s^{p−1} e^{−βs²} e^{βs x₀₀} ds` (the fluctuation function of defn:fluctuation
evaluated at `a = x₀₀ = ξ(0)`, in the `s = √t` variable), and `A_p > 0` when `y₀₀ = η(0) > 0`. -/
theorem headline_leading_coefficient (β : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (p : ℝ) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p)
    (x y : ℕ × ℕ → ℝ) :
    canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p
        = y (0, 0) / ((k₁ : ℝ) * k₂) * logMoment β p 0 (fun s => Real.exp (β * s * x (0, 0)))
      ∧ (0 < y (0, 0) → 0 < canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) p) :=
  ⟨leading_log_coeff β h₁ h₂ k₁ k₂ hk₁ hk₂ p hp₁ hp₂ x y,
    leading_log_coeff_pos β h₁ h₂ k₁ k₂ hβ hk₁ hk₂ p hp₁ hp₂ x y⟩

/-! ### Taylor data -/

/-- **Taylor-data identification**: the input arrays are the Taylor coefficients of the phase:
if `ξ(u,v) = ∑ x_{ij} u^i v^j` on the open ball `|u|, |v| < ρ`, then
`∂_v^j ∂_u^i ξ(0,0) = i! j! x_{ij}`; in particular the arrays are determined by the functions. -/
theorem headline_taylor_data (ρ : ℝ) (hρ : 0 < ρ) (x : ℕ × ℕ → ℝ) (hx : WSummable ρ x)
    (ξ : ℝ → ℝ → ℝ) (hξ : ∀ u v, |u| < ρ → |v| < ρ → ξ u v = dblSum x u v) (i j : ℕ) :
    iteratedDeriv j (fun v => iteratedDeriv i (fun u => ξ u v) 0) 0
      = (i.factorial : ℝ) * (j.factorial : ℝ) * x (i, j) :=
  taylorData_of_eq_dblSum ρ hρ x hx ξ hξ i j

/-! ### Expectation (averaging over a parameter) -/

/-- **The Taylor tree commutes with averaging** over a probability space of jointly measurable
amplitude data with a common envelope:
`E[Z_w(N)] = ∑ N^{−α}(E[A_α] log N + E[B_α]) + O(N^{−2T}(1+log N))`
for every `N ≥ 1`, with the uniform constant. (Only joint measurability of the data is assumed.) -/
theorem headline_expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (β b p₁ p₂ ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁)
    (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂) (c : Ω → ℕ × ℕ → ℝ → ℝ)
    (hcc : ∀ w ij, Continuous (c w ij)) (hcm : ∀ ij, Measurable fun p : Ω × ℝ => c p.1 ij p.2)
    (H : Ω → ℝ → ℝ) (hH : ∀ w, Continuous (H w))
    (hc : ∀ w ij s, |c w ij s| * ρ ^ (ij.1 + ij.2) ≤ H w s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ w s, 0 ≤ s → H w s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (T N : ℝ)
    (hN : 1 ≤ N) :
    |(∫ w, twoDAmp β b N h₁ h₂ k₁ k₂ (anaAmp (c w) b) ∂μ)
        - ∑ α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T,
            N ^ (-α) * ((∫ w, canonA β h₁ h₂ k₁ k₂ (fun i j s => c w (i, j) s) α ∂μ)
                * Real.log N
              + ∫ w, canonB β b h₁ h₂ k₁ k₂ (anaFaceU (c w) b) (anaFaceV (c w) b)
                  (fun i j s => c w (i, j) s) α ∂μ)|
      ≤ uniformTreeConst β b ρ C₀ L p₁ p₂ T h₁ h₂ k₁ k₂ D
        * (N ^ (-(2 * T)) * (1 + Real.log N)) :=
  twoD_taylor_tree_expectation' μ β b p₁ p₂ ρ C₀ L h₁ h₂ k₁ k₂ D hβ hb hbρ hk₁ hk₂ hp₁ hp₂ c hcc
    hcm H hH hc hC₀ henv T N hN

/-! ### Fluctuations (§4.3, thm:strataempiricalexpansion at chart level) -/

/-- **Coefficient continuity**: the canonical coefficients are locally Lipschitz in the Taylor data
(weighted norm `‖·‖_ρ`), the continuity the paper attributes to prop:convergence. -/
theorem headline_coefficient_lipschitz (β ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β) (hρ : 0 < ρ)
    (hr0 : 0 < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (x x' y y' : ℕ × ℕ → ℝ)
    (hx : WSummable ρ x) (hx' : WSummable ρ x') (hy : WSummable ρ y) (hy' : WSummable ρ y')
    (Mx My : ℝ) (hMx : wnorm ρ x ≤ Mx) (hMx' : wnorm ρ x' ≤ Mx) (hMy : wnorm ρ y ≤ My)
    (hMy' : wnorm ρ y' ≤ My) (α : ℝ) (hα : 0 < α) :
    |canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x y (i, j) s) α
        - canonA β h₁ h₂ k₁ k₂ (fun i j s => ampCoeff β x' y' (i, j) s) α|
      ≤ lipA β ρ r h₁ h₂ k₁ k₂ Mx α
          * (wnorm ρ (fun k => y k - y' k) + 2 * β * My * wnorm ρ (fun k => x k - x' k)) :=
  abs_canonA_ampCoeff_sub_le β ρ r h₁ h₂ k₁ k₂ hβ hρ hr0 hrρ hk₁ hk₂ x x' y y' hx hx' hy hy' Mx My
    hMx hMx' hMy hMy' α hα

section Probabilistic

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
  [∀ i, IsProbabilityMeasure (μ i)] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
  [IsProbabilityMeasure μ'] {l : Filter ι}

/-- **Coefficients converge in distribution** (`C_{μ,m}(ξ_n) → C_{μ,m}(G)`): if the random Taylor
data converge in distribution in the coefficient-pair space, so does every finite vector of
canonical coefficients `(A_{α_i}, B_{α_i})_i`. -/
theorem headline_coefficients_in_distribution (β b ρ r : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) {m : ℕ}
    (αs : Fin m → ℝ) (hαs : ∀ i, 0 < αs i) (X : (i : ι) → Ω i → CoeffPair) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun n => coeffVec β b ρ h₁ h₂ k₁ k₂ αs ∘ X n) l
      (coeffVec β b ρ h₁ h₂ k₁ k₂ αs ∘ Z) μ μ' :=
  tendstoInDistribution_coeffVec β b ρ r h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ αs hαs X Z hX

end Probabilistic

section NormalisedRemainders

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

/-- **Ordered normalised remainders converge in distribution** (the second conclusion of
thm:strataempiricalexpansion, chart level): for measurable random Taylor data `X n` converging in
distribution to `Z` and a scale `N_n → ∞`, for every retained exponent `α`,
`(Z_{N_n}(X n) − L_{<α}) / (N_n^{−α} log N_n) ⇒ A_α(Z)` and
`(Z_{N_n}(X n) − L_{<α} − N_n^{−α} A_α(X n) log N_n) / N_n^{−α} ⇒ B_α(Z)`. -/
theorem headline_normalised_remainders (β b p₁ p₂ ρ r T : ℝ) (h₁ h₂ k₁ k₂ : ℕ) (hβ : 0 < β)
    (hb : 0 < b) (hbρ : b < ρ) (hbr : b < r) (hrρ : r < ρ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hp₁ : ((h₁ : ℝ) + 1) / k₁ = p₁) (hp₂ : ((h₂ : ℝ) + 1) / k₂ = p₂)
    (X : ι → Ω → CoeffPair) (hXm : ∀ n, Measurable (X n)) (Z : Ω' → CoeffPair)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) (α : ℝ) (hα : α ∈ polesBelowGen h₁ h₂ k₁ k₂ p₁ p₂ T) :
    TendstoInDistribution (fun n ω => normA β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)) l
        (coeffA β ρ h₁ h₂ k₁ k₂ α ∘ Z) (fun _ => μ) μ'
      ∧ TendstoInDistribution (fun n ω => normB β b ρ p₁ p₂ T h₁ h₂ k₁ k₂ α (Nseq n) (X n ω)) l
        (coeffB β b ρ h₁ h₂ k₁ k₂ α ∘ Z) (fun _ => μ) μ' :=
  ⟨tendstoInDistribution_normA' β b p₁ p₂ ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ hp₁ hp₂ X
      hXm Z hX Nseq hN α hα,
    tendstoInDistribution_normB' β b p₁ p₂ ρ r T h₁ h₂ k₁ k₂ hβ hb hbρ hbr hrρ hk₁ hk₂ hp₁ hp₂ X
      hXm Z hX Nseq hN α hα⟩

end NormalisedRemainders

/-- **The far-phase region is exponentially negligible** (the `Z_n^{(2)}` step of
thm:strataempiricalexpansion): on a measurable set where the phase is `≥ ε` and the fluctuation is
bounded by `M`, `|∫_E η e^{−βnK + β√(nK)ψ}| ≤ (∫_E |η|) e^{−βnε/2 + βM²/2}`. -/
theorem headline_far_phase {W : Type*} [MeasurableSpace W] (μ : Measure W) (E : Set W)
    (hE : MeasurableSet E) (β n ε M : ℝ) (hβ : 0 < β) (hn : 0 ≤ n) (hε : 0 ≤ ε)
    (η K ψ : W → ℝ) (hK : ∀ w ∈ E, ε ≤ K w) (hψ : ∀ w ∈ E, |ψ w| ≤ M)
    (hη : IntegrableOn η E μ) :
    |∫ w in E, η w * Real.exp (-β * n * K w + β * Real.sqrt (n * K w) * ψ w) ∂μ|
      ≤ (∫ w in E, |η w| ∂μ) * Real.exp (-β * n * ε / 2 + β * M ^ 2 / 2) :=
  farPhase_bound μ E hE β n ε M hβ hn hε η K ψ hK hψ hη

end Laplace.Grammar
