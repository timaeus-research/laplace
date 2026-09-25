/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.StateDensity

/-!
# The Tauberian variance theorem: regular variation of `Z` gives `u² Var_u(ℓ) → λ`

Let `ν` be a state density (a measure on `[0, ∞)`) with Laplace transform `Z(u) = ∫ e^{-uℓ} dν`.
If `Z` is regularly varying at infinity with index `−λ`, i.e. `Z(cu)/Z(u) → c^{-λ}` for every
`c > 0`, then the tilted first moment satisfies `u⟨ℓ⟩_u → λ`, the tilted second moment satisfies
`u²⟨ℓ²⟩_u → λ(λ+1)`, and therefore

  `u² Var_{ν_u}(ℓ) → λ`   (`tendsto_sq_mul_lawVar_of_regVar`).

**No derivative control of `Z` is needed.** The proof is a monotone-density argument done directly
on the integrals: for `c > 1` the elementary sandwich `x e^{-x} ≤ 1 − e^{-x} ≤ x` gives

  `(c−1) u N₁(cu) ≤ Z(u) − Z(cu) ≤ (c−1) u N₁(u)`,   `N₁(u) = ∫ ℓ e^{-uℓ} dν`

(`sandwich_tilt`), which squeezes `u N₁(u)/Z(u)` between `(1 − c^{-λ})/(c−1)` and
`c^{λ+1}(1 − c^{-λ})/(c−1)` in the limit; both tend to `λ` as `c ↓ 1` (`tendsto_ratio_of_regVar`).
The same argument with the weight `ℓ` gives `u N₂/N₁ → λ + 1`.

In particular Watanabe's asymptotic `Z(u) ~ C u^{-λ} (log u)^{m-1}` implies regular variation
(`regVar_of_asymptotic`), so **the partition-function asymptotic alone determines the leading
featureless-line geometry**: `u² Var_u(L) → λ` (`tendsto_sq_mul_priorCov_of_partition_asymptotic`),
and hence, by `ThermoLengthAsymptotic`, the radial response length grows like `√λ log t`
(Astra, round 25, item 2).
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### The elementary sandwich -/

/-- `x e^{-x} ≤ 1 − e^{-x} ≤ x` for `x ≥ 0`. -/
theorem exp_neg_sandwich (x : ℝ) :
    x * Real.exp (-x) ≤ 1 - Real.exp (-x) ∧ 1 - Real.exp (-x) ≤ x := by
  constructor
  · have h := Real.add_one_le_exp x
    have hF : 0 < Real.exp (-x) := Real.exp_pos _
    have : (x + 1) * Real.exp (-x) ≤ 1 := by
      calc (x + 1) * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
            mul_le_mul_of_nonneg_right h hF.le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    linarith
  · have := Real.add_one_le_exp (-x)
    linarith

/-- The tilted moments of a state density: `∫ ℓ^k e^{-uℓ} dν`. -/
noncomputable def lawMoment (ν : Measure ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∫ ℓ, ℓ ^ k * Real.exp (-(u * ℓ)) ∂ν

/-- **The sandwich for tilted integrals with a nonnegative weight**: for `c > 1`,
`(c−1) u ∫ w ℓ e^{-cuℓ} ≤ ∫ w e^{-uℓ} − ∫ w e^{-cuℓ} ≤ (c−1) u ∫ w ℓ e^{-uℓ}`. -/
theorem sandwich_tilt (ν : Measure ℝ) {w : ℝ → ℝ} (hw : ∀ᵐ ℓ ∂ν, 0 ≤ w ℓ)
    (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {c u : ℝ} (hc : 1 < c) (hu : 0 < u)
    (h0 : Integrable (fun ℓ ↦ w ℓ * Real.exp (-(u * ℓ))) ν)
    (h0' : Integrable (fun ℓ ↦ w ℓ * Real.exp (-(c * u * ℓ))) ν)
    (h1 : Integrable (fun ℓ ↦ w ℓ * ℓ * Real.exp (-(u * ℓ))) ν)
    (h1' : Integrable (fun ℓ ↦ w ℓ * ℓ * Real.exp (-(c * u * ℓ))) ν) :
    (c - 1) * u * ∫ ℓ, w ℓ * ℓ * Real.exp (-(c * u * ℓ)) ∂ν ≤
        (∫ ℓ, w ℓ * Real.exp (-(u * ℓ)) ∂ν) - ∫ ℓ, w ℓ * Real.exp (-(c * u * ℓ)) ∂ν ∧
      (∫ ℓ, w ℓ * Real.exp (-(u * ℓ)) ∂ν) - (∫ ℓ, w ℓ * Real.exp (-(c * u * ℓ)) ∂ν) ≤
        (c - 1) * u * ∫ ℓ, w ℓ * ℓ * Real.exp (-(u * ℓ)) ∂ν := by
  rw [← integral_sub h0 h0', ← integral_const_mul, ← integral_const_mul]
  have hcu : 0 < (c - 1) * u := by nlinarith
  -- the pointwise inequalities
  have hpt : ∀ᵐ ℓ ∂ν, (c - 1) * u * (w ℓ * ℓ * Real.exp (-(c * u * ℓ))) ≤
      w ℓ * Real.exp (-(u * ℓ)) - w ℓ * Real.exp (-(c * u * ℓ)) ∧
      w ℓ * Real.exp (-(u * ℓ)) - w ℓ * Real.exp (-(c * u * ℓ)) ≤
        (c - 1) * u * (w ℓ * ℓ * Real.exp (-(u * ℓ))) := by
    filter_upwards [hw, hpos] with ℓ hwℓ hℓ
    obtain ⟨hlow, hup⟩ := exp_neg_sandwich ((c - 1) * u * ℓ)
    have hsplit : Real.exp (-(c * u * ℓ)) =
        Real.exp (-(u * ℓ)) * Real.exp (-((c - 1) * u * ℓ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hE : 0 ≤ Real.exp (-(u * ℓ)) := (Real.exp_pos _).le
    have hwE : 0 ≤ w ℓ * Real.exp (-(u * ℓ)) := mul_nonneg hwℓ hE
    rw [hsplit]
    constructor
    · have := mul_le_mul_of_nonneg_left hlow hwE
      nlinarith
    · have := mul_le_mul_of_nonneg_left hup hwE
      nlinarith
  constructor
  · exact integral_mono_ae (h1'.const_mul _) (h0.sub h0') (hpt.mono fun ℓ h ↦ h.1)
  · exact integral_mono_ae (h0.sub h0') (h1.const_mul _) (hpt.mono fun ℓ h ↦ h.2)

/-! ### The abstract regular-variation squeeze -/

/-- `(1 − c^{-λ})/(c − 1) → λ` as `c ↓ 1`. -/
theorem tendsto_regVar_lower (lam : ℝ) :
    Tendsto (fun c : ℝ ↦ (1 - c ^ (-lam)) / (c - 1)) (𝓝[>] 1) (𝓝 lam) := by
  have h := (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := -lam) (Or.inl one_ne_zero))
  rw [hasDerivAt_iff_tendsto_slope] at h
  have h' := (h.mono_left (nhdsWithin_mono _ fun c (hc : 1 < c) ↦ ne_of_gt hc)).neg
  simp only [Real.one_rpow, mul_one, neg_neg] at h'
  refine h'.congr fun c ↦ ?_
  rw [slope_def_field, Real.one_rpow]
  ring

/-- `c^{λ+1}(1 − c^{-λ})/(c − 1) → λ` as `c ↓ 1`. -/
theorem tendsto_regVar_upper (lam : ℝ) :
    Tendsto (fun c : ℝ ↦ c * ((1 - c ^ (-lam)) / (c - 1)) / c ^ (-lam)) (𝓝[>] 1) (𝓝 lam) := by
  have h1 := tendsto_regVar_lower lam
  have h2 : Tendsto (fun c : ℝ ↦ c) (𝓝[>] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun c : ℝ ↦ c ^ (-lam)) (𝓝[>] 1) (𝓝 1) := by
    have := (Real.continuousAt_rpow_const 1 (-lam) (Or.inl one_ne_zero)).tendsto
    rw [Real.one_rpow] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := (h2.mul h1).div h3 one_ne_zero
  have e : (1 : ℝ) * lam / 1 = lam := by ring
  rw [e] at this
  exact this

/-- **The regular-variation squeeze**: if `F(cu)/F(u) → c^{-λ}` and `G` is sandwiched by the
increments of `F`, then `u G(u)/F(u) → λ`. -/
theorem tendsto_ratio_of_regVar {F G : ℝ → ℝ} {lam : ℝ}
    (hF : ∀ᶠ u in atTop, 0 < F u)
    (hreg : ∀ c > 0, Tendsto (fun u ↦ F (c * u) / F u) atTop (𝓝 (c ^ (-lam))))
    (hsand : ∀ c > 1, ∀ᶠ u in atTop, (c - 1) * u * G (c * u) ≤ F u - F (c * u) ∧
      F u - F (c * u) ≤ (c - 1) * u * G u) :
    Tendsto (fun u ↦ u * G u / F u) atTop (𝓝 lam) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose `c` close to `1`
  have hA := (tendsto_regVar_lower lam).eventually (Metric.ball_mem_nhds lam (half_pos hε))
  have hB := (tendsto_regVar_upper lam).eventually (Metric.ball_mem_nhds lam (half_pos hε))
  have : NeBot (𝓝[>] (1 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  obtain ⟨c, ⟨hcA, hcB⟩, hc⟩ := ((hA.and hB).and self_mem_nhdsWithin).exists
  have hc : 1 < c := hc
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  rw [Real.dist_eq] at hcA hcB
  have hQ := hreg c hc0
  have hcuT : Tendsto (fun u : ℝ ↦ c * u) atTop atTop := Tendsto.const_mul_atTop hc0 tendsto_id
  -- the two eventual bounds
  have hlow : ∀ᶠ u in atTop, lam - ε < u * G u / F u := by
    have hlim : Tendsto (fun u ↦ (1 - F (c * u) / F u) / (c - 1)) atTop
        (𝓝 ((1 - c ^ (-lam)) / (c - 1))) :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hQ).div_const _
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds _ (half_pos hε)), hsand c hc, hF,
      hcuT.eventually hF, eventually_gt_atTop (0 : ℝ)] with u hu hs hFu hFcu hu0
    rw [Real.dist_eq] at hu
    have hR : (1 - F (c * u) / F u) / (c - 1) ≤ u * G u / F u := by
      have e : (1 - F (c * u) / F u) / (c - 1) = (F u - F (c * u)) / (c - 1) / F u := by
        field_simp
      rw [e]
      refine div_le_div_of_nonneg_right ?_ hFu.le
      rw [div_le_iff₀ (by linarith)]
      linarith [hs.2]
    rw [abs_lt] at hu hcA
    linarith
  have hup : ∀ᶠ u in atTop, u * G u / F u < lam + ε := by
    have hlim : Tendsto (fun u ↦ c * ((1 - F (c * u) / F u) / (c - 1)) / (F (c * u) / F u)) atTop
        (𝓝 (c * ((1 - c ^ (-lam)) / (c - 1)) / c ^ (-lam))) :=
      (((tendsto_const_nhds (x := c)).mul
        (((tendsto_const_nhds (x := (1 : ℝ))).sub hQ).div_const _)).div hQ
        (by positivity))
    have hev : ∀ᶠ u in atTop, c * u * G (c * u) / F (c * u) < lam + ε := by
      filter_upwards [hlim.eventually (Metric.ball_mem_nhds _ (half_pos hε)), hsand c hc, hF,
        hcuT.eventually hF, eventually_gt_atTop (0 : ℝ)] with u hu hs hFu hFcu hu0
      rw [Real.dist_eq] at hu
      have hR : c * u * G (c * u) / F (c * u) ≤
          c * ((1 - F (c * u) / F u) / (c - 1)) / (F (c * u) / F u) := by
        have e : c * ((1 - F (c * u) / F u) / (c - 1)) / (F (c * u) / F u) =
            (c * ((F u - F (c * u)) / (c - 1))) / F (c * u) := by
          field_simp
        rw [e]
        refine div_le_div_of_nonneg_right ?_ hFcu.le
        rw [mul_div_assoc', le_div_iff₀ (by linarith)]
        linarith [mul_le_mul_of_nonneg_left hs.1 hc0.le]
      rw [abs_lt] at hu hcB
      linarith
    -- transport from `c u` to `u`
    rw [eventually_atTop] at hev ⊢
    obtain ⟨U, hU⟩ := hev
    refine ⟨c * U, fun v hv ↦ ?_⟩
    have := hU (v / c) (by rw [le_div_iff₀ hc0]; linarith)
    rwa [mul_div_cancel₀ _ hc0.ne'] at this
  obtain ⟨U₁, h₁⟩ := eventually_atTop.mp hlow
  obtain ⟨U₂, h₂⟩ := eventually_atTop.mp hup
  refine ⟨max U₁ U₂, fun u hu ↦ ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [h₁ u (le_trans (le_max_left _ _) hu)]
  · linarith [h₂ u (le_trans (le_max_right _ _) hu)]

/-! ### The Tauberian variance theorem -/

/-- Regular variation of a state density's Laplace transform with index `−λ`. -/
def RegVar (ν : Measure ℝ) (lam : ℝ) : Prop :=
  ∀ c > 0, Tendsto (fun u ↦ lawMoment ν 0 (c * u) / lawMoment ν 0 u) atTop (𝓝 (c ^ (-lam)))

/-- **The first-moment Tauberian theorem**: `u⟨ℓ⟩_u → λ`. -/
theorem tendsto_mul_lawMoment_one_div_of_regVar (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ)
    (hint : ∀ u > 0, ∀ k ≤ 2, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(u * ℓ))) ν)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) {lam : ℝ} (hreg : RegVar ν lam) :
    Tendsto (fun u ↦ u * lawMoment ν 1 u / lawMoment ν 0 u) atTop (𝓝 lam) := by
  refine tendsto_ratio_of_regVar (F := lawMoment ν 0) (G := lawMoment ν 1)
    ((eventually_gt_atTop 0).mono fun u hu ↦ hZ u hu) hreg fun c hc ↦ ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hcu : 0 < c * u := by positivity
  have h := sandwich_tilt ν (w := fun _ ↦ (1 : ℝ)) (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    hpos hc hu (by simpa using hint u hu 0 (by norm_num))
    (by simpa using hint (c * u) hcu 0 (by norm_num))
    (by simpa using hint u hu 1 (by norm_num)) (by simpa using hint (c * u) hcu 1 (by norm_num))
  simpa [lawMoment] using h

/-- **The second-moment Tauberian theorem**: `u N₂(u)/N₁(u) → λ + 1`. -/
theorem tendsto_mul_lawMoment_two_div_of_regVar (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ)
    (hint : ∀ u > 0, ∀ k ≤ 2, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(u * ℓ))) ν)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) {lam : ℝ} (hlam : 0 < lam) (hreg : RegVar ν lam) :
    Tendsto (fun u ↦ u * lawMoment ν 2 u / lawMoment ν 1 u) atTop (𝓝 (lam + 1)) := by
  have hR := tendsto_mul_lawMoment_one_div_of_regVar ν hpos hint hZ hreg
  have hN₁ : ∀ᶠ u in atTop, 0 < lawMoment ν 1 u := by
    filter_upwards [hR.eventually (lt_mem_nhds hlam), eventually_gt_atTop (0 : ℝ)] with u hu hu0
    have hZu := hZ u hu0
    by_contra hneg
    push Not at hneg
    have : u * lawMoment ν 1 u / lawMoment ν 0 u ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hu0.le hneg) hZu.le
    linarith
  -- regular variation of `N₁` with index `−(λ+1)`
  have hreg' : ∀ c > 0, Tendsto (fun u ↦ lawMoment ν 1 (c * u) / lawMoment ν 1 u) atTop
      (𝓝 (c ^ (-(lam + 1)))) := fun c hc ↦ by
    have hcu : Tendsto (fun u : ℝ ↦ c * u) atTop atTop := Tendsto.const_mul_atTop hc tendsto_id
    have hRc := hR.comp hcu
    have hlim := ((hRc.div hR hlam.ne').mul (hreg c hc)).div_const c
    have e : (c ^ (-lam) : ℝ) / c = c ^ (-(lam + 1)) := by
      rw [neg_add, Real.rpow_add hc, Real.rpow_neg_one, div_eq_mul_inv]
    rw [div_self hlam.ne', one_mul, e] at hlim
    refine hlim.congr' ?_
    filter_upwards [hN₁, hcu.eventually hN₁, eventually_gt_atTop (0 : ℝ)] with u h1 h1' hu0
    have hZu := (hZ u hu0).ne'
    have hZcu := (hZ (c * u) (by positivity)).ne'
    simp only [Pi.div_apply, Function.comp_apply]
    field_simp
  refine tendsto_ratio_of_regVar (F := lawMoment ν 1) (G := lawMoment ν 2) hN₁ hreg'
    fun c hc ↦ ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hcu : 0 < c * u := by positivity
  have h := sandwich_tilt ν (w := fun ℓ ↦ ℓ) hpos hpos hc hu
    (by simpa using hint u hu 1 (by norm_num)) (by simpa using hint (c * u) hcu 1 (by norm_num))
    ((hint u hu 2 (by norm_num)).congr (Filter.Eventually.of_forall fun ℓ ↦ by ring))
    ((hint (c * u) hcu 2 (by norm_num)).congr (Filter.Eventually.of_forall fun ℓ ↦ by ring))
  simp only [lawMoment, pow_one]
  have e : ∀ v, (∫ ℓ, ℓ ^ 2 * Real.exp (-(v * ℓ)) ∂ν) = ∫ ℓ, ℓ * ℓ * Real.exp (-(v * ℓ)) ∂ν :=
    fun v ↦ integral_congr_ae (Filter.Eventually.of_forall fun ℓ ↦ by ring)
  rw [e, e]
  exact h

/-- **The Tauberian variance theorem**: regular variation of `Z` with index `−λ` gives
`u² Var_{ν_u}(ℓ) → λ`. -/
theorem tendsto_sq_mul_lawVar_of_regVar (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ)
    (hint : ∀ u > 0, ∀ k ≤ 2, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(u * ℓ))) ν)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) {lam : ℝ} (hlam : 0 < lam) (hreg : RegVar ν lam) :
    Tendsto (fun u ↦ u ^ 2 * lawVar ν u) atTop (𝓝 lam) := by
  have hR := tendsto_mul_lawMoment_one_div_of_regVar ν hpos hint hZ hreg
  have hR₂ := tendsto_mul_lawMoment_two_div_of_regVar ν hpos hint hZ hlam hreg
  have hN₁ : ∀ᶠ u in atTop, 0 < lawMoment ν 1 u := by
    filter_upwards [hR.eventually (lt_mem_nhds hlam), eventually_gt_atTop (0 : ℝ)] with u hu hu0
    have hZu := hZ u hu0
    by_contra hneg
    push Not at hneg
    have : u * lawMoment ν 1 u / lawMoment ν 0 u ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hu0.le hneg) hZu.le
    linarith
  have hlim := (hR₂.mul hR).sub (hR.mul hR)
  have e : (lam + 1) * lam - lam * lam = lam := by ring
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards [hN₁, eventually_gt_atTop (0 : ℝ)] with u h1 hu0
  have hZu := (hZ u hu0).ne'
  unfold lawVar lawExp
  have e2 : (∫ ℓ, ℓ * ℓ * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 2 u :=
    integral_congr_ae (Filter.Eventually.of_forall fun ℓ ↦ by ring)
  have e1 : (∫ ℓ, ℓ * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 1 u := by simp [lawMoment]
  have e0 : (∫ ℓ, Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 0 u := by simp [lawMoment]
  rw [e2, e1, e0]
  field_simp

/-! ### From Watanabe's asymptotic to regular variation -/

/-- `Z(u) ~ C u^{-λ} (log u)^k` with `C > 0` implies regular variation with index `−λ`. -/
theorem regVar_of_asymptotic (ν : Measure ℝ) {lam C : ℝ} (k : ℕ) (hC : 0 < C)
    (hasym : Tendsto (fun u ↦ lawMoment ν 0 u / (u ^ (-lam) * Real.log u ^ k)) atTop (𝓝 C)) :
    RegVar ν lam := by
  intro c hc
  have hcu : Tendsto (fun u : ℝ ↦ c * u) atTop atTop := Tendsto.const_mul_atTop hc tendsto_id
  have hasym' := hasym.comp hcu
  -- the log ratio tends to `1`
  have hlog : Tendsto (fun u ↦ Real.log (c * u) / Real.log u) atTop (𝓝 1) := by
    have h1 : Tendsto (fun u ↦ Real.log c / Real.log u) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have h2 := h1.const_add 1
    rw [add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    have hlu : Real.log u ≠ 0 := (Real.log_pos hu).ne'
    rw [Real.log_mul hc.ne' (by linarith)]
    field_simp
    ring
  have hlim := ((hasym'.div hasym hC.ne').mul ((tendsto_const_nhds (x := c ^ (-lam))).mul
    (hlog.pow k)))
  rw [div_self hC.ne', one_mul, one_pow, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_gt_atTop (1 / c)] with u hu huc
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hlu : Real.log u ≠ 0 := (Real.log_pos hu).ne'
  have hcu1 : 1 < c * u := by rwa [div_lt_iff₀ hc, mul_comm] at huc
  have hlcu : Real.log (c * u) ≠ 0 := (Real.log_pos hcu1).ne'
  simp only [Pi.div_apply, Function.comp_apply]
  have hp : (c * u) ^ (-lam) = c ^ (-lam) * u ^ (-lam) := Real.mul_rpow hc.le hu0.le
  rw [hp]
  have hu' : u ^ (-lam) ≠ 0 := (Real.rpow_pos_of_pos hu0 _).ne'
  have hc' : c ^ (-lam) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have hluk : Real.log u ^ k ≠ 0 := pow_ne_zero k hlu
  rw [div_pow]
  field_simp


/-! ### The model-level corollary -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Integrability against the state density in terms of the prior. -/
theorem integrable_lossLaw_iff {π L : X → ℝ} (hπm : Measurable π) (hπ : ∀ x, 0 ≤ π x)
    (hL : Measurable L) {g : ℝ → ℝ} (hg : Measurable g) :
    Integrable g (lossLaw μ π L) ↔ Integrable (fun x ↦ g (L x) * π x) μ := by
  unfold lossLaw
  rw [integrable_map_measure hg.aestronglyMeasurable hL.aemeasurable,
    integrable_withDensity_iff hπm.ennreal_ofReal (ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top)]
  refine ⟨fun h ↦ h.congr (Filter.Eventually.of_forall fun x ↦ ?_),
    fun h ↦ h.congr (Filter.Eventually.of_forall fun x ↦ ?_)⟩ <;>
  simp [Function.comp_apply, ENNReal.toReal_ofReal (hπ x)]

/-- **The partition-function asymptotic determines the leading featureless-line geometry**:
if `Z(u) ~ C u^{-λ} (log u)^k` with `C > 0`, `λ > 0`, then `u² Var_u(L) → λ`. -/
theorem tendsto_sq_mul_priorCov_of_partition_asymptotic {π L : X → ℝ} (hπm : Measurable π)
    (hπ : ∀ x, 0 ≤ π x) (hL : Measurable L) (hL0 : ∀ x, 0 ≤ L x)
    (hint : ∀ u > 0, ∀ k ≤ 2, Integrable (fun x ↦ L x ^ k * Real.exp (-(u * L x)) * π x) μ)
    (hZ : ∀ u > 0, 0 < priorZ μ π L u) {lam C : ℝ} (k : ℕ) (hlam : 0 < lam) (hC : 0 < C)
    (hasym : Tendsto (fun u ↦ priorZ μ π L u / (u ^ (-lam) * Real.log u ^ k)) atTop (𝓝 C)) :
    Tendsto (fun u ↦ u ^ 2 * priorCov μ π L L L u) atTop (𝓝 lam) := by
  have hZ' : ∀ u, lawMoment (lossLaw μ π L) 0 u = priorZ μ π L u := fun u ↦ by
    rw [priorZ_eq_lossLaw hπm hπ hL]
    simp [lawMoment]
  have hpos : ∀ᵐ ℓ ∂(lossLaw μ π L), 0 ≤ ℓ := by
    unfold lossLaw
    rw [ae_map_iff hL.aemeasurable measurableSet_Ici]
    exact ae_of_all _ hL0
  have hint' : ∀ u > 0, ∀ k ≤ 2, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(u * ℓ)))
      (lossLaw μ π L) := fun u hu k hk ↦
    (integrable_lossLaw_iff hπm hπ hL (by fun_prop)).mpr (hint u hu k hk)
  have hZ'' : ∀ u > 0, 0 < lawMoment (lossLaw μ π L) 0 u := fun u hu ↦ by
    rw [hZ']
    exact hZ u hu
  have hreg : RegVar (lossLaw μ π L) lam := by
    refine regVar_of_asymptotic _ k hC ?_
    simp only [hZ']
    exact hasym
  have := tendsto_sq_mul_lawVar_of_regVar _ hpos hint' hZ'' hlam hreg
  refine this.congr fun u ↦ ?_
  rw [priorCov_self_eq_lawVar hπm hπ hL]

end Laplace.Multi
