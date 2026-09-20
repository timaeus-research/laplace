/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WeightedTemperatureAdapter

/-!
# Discharging the localization hypotheses from coercivity

The temperature-level theorem `weightedPolynomial_coefficients_eq_of_superPoly` assumes
(i) `e^{-cP}` integrable for every `c > 0` and (ii) the corrections dominated by the leading
part on the localization region. Both follow from the leading part alone:

* (i) from integrability of `e^{-P}` by the dilation law (`ε^D = c` via a `D`-th root);
* (ii) on the sublevel set `U = {P ≤ δ}` for `δ` small, root-free: the natural-power
  coercivity `|x_i|^D ≤ κ P(x)^{a_i}` gives `|x^α|^D ≤ κ^{|α|} P^{ℓ(α)} ≤ κ^{|α|} δ^{ℓ(α)−D} P^D`
  on `U`, and `δ` is chosen (by continuity in `δ`, for the finitely many `α ∈ S`) so that the
  constant is at most `θ^D`.

Headline: `weightedPolynomial_recovery_of_superPoly` — for every sufficiently small sublevel
localization, superpolynomial agreement of the localized monomial moments forces equal
coefficients.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.Multi

namespace IntWeights

variable {ι : Type*} [Fintype ι] (W : IntWeights ι)

/-! ### Integrability of `e^{-cP}` from `c = 1` -/

omit [Fintype ι] in
/-- Quasi-homogeneity forces `P 0 = 0`. -/
theorem qh_zero {P : (ι → ℝ) → ℝ}
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u) : P 0 = 0 := by
  have h := hPqh 2 two_pos 0
  have hd : W.dil 2 0 = 0 := by
    funext i
    simp [dil]
  rw [hd] at h
  have h2 : (1 : ℝ) < 2 ^ W.D := one_lt_pow₀ (by norm_num) W.D_pos.ne'
  nlinarith

/-- **Integrability of `e^{-cP}` for every `c > 0`** from the case `c = 1`, by the dilation
law with `ε = c^{1/D}`. -/
theorem integrable_exp_neg_mul_of_integrable {P : (ι → ℝ) → ℝ} (hPm : Measurable P)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hint : Integrable fun u : ι → ℝ ↦ Real.exp (-P u)) {c : ℝ} (hc : 0 < c) :
    Integrable fun u : ι → ℝ ↦ Real.exp (-(c * P u)) := by
  set ε : ℝ := c ^ ((W.D : ℝ)⁻¹) with hε_def
  have hε : 0 < ε := Real.rpow_pos_of_pos hc _
  have hεD : ε ^ W.D = c := by
    rw [hε_def, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, inv_mul_cancel₀
      (by exact_mod_cast W.D_pos.ne'), Real.rpow_one]
  have hfm : AEStronglyMeasurable (fun u : ι → ℝ ↦ Real.exp (-P u)) volume :=
    (Real.measurable_exp.comp hPm.neg).aestronglyMeasurable
  have := (W.integrable_comp_dil_iff hε hfm).mpr hint
  refine this.congr (Filter.Eventually.of_forall fun u ↦ ?_)
  simp only []
  rw [hPqh ε hε, hεD]

/-! ### Domination of the corrections on a small sublevel set -/

/-- The total degree of a monomial exponent. -/
def totalDeg (α : ι → ℕ) : ℕ := ∑ i, α i

/-- The `D`-th power of a monomial is controlled by `κ^{|α|} P^{ℓ(α)}`. -/
theorem pow_abs_mvMonomial_le {P : (ι → ℝ) → ℝ} {κ : ℝ}
    (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i) (α : ι → ℕ) (x : ι → ℝ) :
    |mvMonomial α x| ^ W.D ≤ κ ^ totalDeg α * P x ^ W.wdeg α := by
  unfold mvMonomial totalDeg wdeg
  rw [Finset.abs_prod, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ ↦ by positivity) fun i _ ↦ ?_
  rw [abs_pow, ← pow_mul, mul_comm (α i) W.D, pow_mul, pow_mul]
  calc (|x i| ^ W.D) ^ α i ≤ (κ * P x ^ W.a i) ^ α i :=
        pow_le_pow_left₀ (by positivity) (hcoer x i) _
    _ = κ ^ α i * (P x ^ W.a i) ^ α i := mul_pow _ _ _

/-- For every `θ > 0` there is `δ > 0` such that the weighted polynomial is dominated by
`θ P` on the sublevel set `{P ≤ δ}`. -/
theorem exists_dominated_of_coercive {P : (ι → ℝ) → ℝ} (hP0 : ∀ u, 0 ≤ P u) {κ : ℝ}
    (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i) (S : Finset (ι → ℕ))
    (c : (ι → ℕ) → ℝ) (hS : ∀ α ∈ S, W.D < W.wdeg α) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, P x ≤ δ → |wpoly S c x| ≤ θ * P x := by
  -- the per-monomial share of `θ`
  set M : ℝ := ∑ α ∈ S, |c α| with hM_def
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  set θ' : ℝ := θ / (M + 1) with hθ'_def
  have hθ' : 0 < θ' := div_pos hθ (by linarith)
  -- choose `δ` with `κ^{|α|} δ^{ℓ(α)−D} ≤ θ'^D` for every `α ∈ S`
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ α ∈ S,
      κ ^ totalDeg α * δ ^ (W.wdeg α - W.D) ≤ θ' ^ W.D := by
    rw [Filter.eventually_all_finset]
    intro α hα
    have hlim : Tendsto (fun δ : ℝ ↦ κ ^ totalDeg α * δ ^ (W.wdeg α - W.D)) (𝓝[>] (0 : ℝ))
        (𝓝 0) := by
      have hcont : Continuous fun δ : ℝ ↦ κ ^ totalDeg α * δ ^ (W.wdeg α - W.D) := by
        fun_prop
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [zero_pow (by have := hS α hα; omega), mul_zero] at this
    exact hlim.eventually_le_const (by positivity)
  obtain ⟨δ, hδS, hδ⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδ
  refine ⟨δ, hδ0, fun x hx ↦ ?_⟩
  have hPx := hP0 x
  -- each monomial is at most `θ' P x`
  have hmono : ∀ α ∈ S, |mvMonomial α x| ≤ θ' * P x := by
    intro α hα
    have h1 := W.pow_abs_mvMonomial_le hcoer α x
    have hsplit : P x ^ W.wdeg α = P x ^ (W.wdeg α - W.D) * P x ^ W.D := by
      rw [← pow_add, Nat.sub_add_cancel (hS α hα).le]
    have h2 : P x ^ (W.wdeg α - W.D) ≤ δ ^ (W.wdeg α - W.D) := pow_le_pow_left₀ hPx hx _
    have h3 : |mvMonomial α x| ^ W.D ≤ (θ' * P x) ^ W.D := by
      calc |mvMonomial α x| ^ W.D ≤ κ ^ totalDeg α * P x ^ W.wdeg α := h1
        _ = κ ^ totalDeg α * P x ^ (W.wdeg α - W.D) * P x ^ W.D := by rw [hsplit]; ring
        _ ≤ κ ^ totalDeg α * δ ^ (W.wdeg α - W.D) * P x ^ W.D := by gcongr
        _ ≤ θ' ^ W.D * P x ^ W.D :=
            mul_le_mul_of_nonneg_right (hδS α hα) (by positivity)
        _ = (θ' * P x) ^ W.D := (mul_pow _ _ _).symm
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) W.D_pos.ne').mp h3
  unfold wpoly
  calc |∑ α ∈ S, c α * mvMonomial α x| ≤ ∑ α ∈ S, |c α| * |mvMonomial α x| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ ↦ ?_)
        rw [abs_mul]
    _ ≤ ∑ α ∈ S, |c α| * (θ' * P x) :=
        Finset.sum_le_sum fun α hα ↦ mul_le_mul_of_nonneg_left (hmono α hα) (abs_nonneg _)
    _ = M * θ' * P x := by rw [← Finset.sum_mul]; ring
    _ ≤ θ * P x := by
        apply mul_le_mul_of_nonneg_right _ hPx
        rw [hθ'_def]
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

omit [Fintype ι] in
/-- The sublevel set is a measurable neighbourhood of the origin. -/
theorem sublevel_mem_nhds {P : (ι → ℝ) → ℝ} (hPc : Continuous P)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u) {δ : ℝ} (hδ : 0 < δ) :
    {x : ι → ℝ | P x ≤ δ} ∈ 𝓝 (0 : ι → ℝ) := by
  have h0 : P 0 < δ := by rw [W.qh_zero hPqh]; exact hδ
  exact hPc.continuousAt.preimage_mem_nhds (Iic_mem_nhds h0)

/-! ### The self-contained headline -/

/-- **Semi-quasi-homogeneous polynomial recovery from the leading part alone**: for a
continuous, nonnegative, quasi-homogeneous, coercive leading part `P` with `e^{-P}`
integrable, there is `δ₀ > 0` such that for every sublevel localization `{P ≤ δ}`,
`0 < δ ≤ δ₀`, superpolynomial agreement in the temperature of the localized normalized
moments of the monomials `x^α`, `α ∈ S`, for the two losses `P + ∑ c_j α x^α` forces
`c₁ = c₂` on `S`. -/
theorem weightedPolynomial_recovery_of_superPoly {P : (ι → ℝ) → ℝ} (hPc : Continuous P)
    (hP0 : ∀ u, 0 ≤ P u)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hint : Integrable fun u : ι → ℝ ↦ Real.exp (-P u))
    {κ : ℝ} (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i)
    (S : Finset (ι → ℕ)) (c₁ c₂ : (ι → ℕ) → ℝ) (hS : ∀ α ∈ S, W.D < W.wdeg α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      (∀ α ∈ S, Laplace.SuperPoly fun t : ℝ ↦
        tempMoment {x : ι → ℝ | P x ≤ δ} (wLoss P S c₂) (mvMonomial α) t -
          tempMoment {x : ι → ℝ | P x ≤ δ} (wLoss P S c₁) (mvMonomial α) t) →
      ∀ α ∈ S, c₁ α = c₂ α := by
  obtain ⟨δ₁, hδ₁, hdom₁⟩ := W.exists_dominated_of_coercive hP0 hκ hcoer S c₁ hS
    (θ := 1 / 2) (by norm_num)
  obtain ⟨δ₂, hδ₂, hdom₂⟩ := W.exists_dominated_of_coercive hP0 hκ hcoer S c₂ hS
    (θ := 1 / 2) (by norm_num)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hδle hdata ↦ ?_⟩
  have hPm : Measurable P := hPc.measurable
  refine W.weightedPolynomial_coefficients_eq_of_superPoly hPm hP0 hPqh
    (fun c hc ↦ W.integrable_exp_neg_mul_of_integrable hPm hPqh hint hc) hκ hcoer
    (measurableSet_le hPm measurable_const) (W.sublevel_mem_nhds hPc hPqh hδ) S c₁ c₂ hS
    (c₀ := 1 / 2) (by norm_num) ?_ ?_ hdata
  · intro x hx
    have := hdom₁ x (le_trans hx (hδle.trans (min_le_left _ _)))
    norm_num
    exact this
  · intro x hx
    have := hdom₂ x (le_trans hx (hδle.trans (min_le_right _ _)))
    norm_num
    exact this

end IntWeights

end Laplace.Multi
