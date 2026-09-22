/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RelativeChartLeading
import Laplace.Multi.SingularPowerNormalForm

/-!
# Attenuating a pattern is tempering its directions

A mixture truth `q_θ = (1 − θ) q_base + θ q_P` has population loss `L_θ = (1 − θ) L_base + θ L_P`,
affine in the mixture weight `θ` of the pattern `P`. At a common minimiser the germ of `L_θ` is the
base germ in the transverse directions plus `θ` times the pattern loss along the base-optimal set,
so the posterior at temperature `t` sees the pattern-specific directions at temperature `θ t`.

* **Separable attenuation identity.** For `L(x, y) = f(x) + θ g(y)` with a product cutoff,
  `Z(t) = Z_f(t) · Z_g(θ t)` exactly (`attZ_separable`), and the energy splits as
  `t E[L] = t E_f[f](t) + (θ t) E_g[g](θ t)` (`mul_attExp_separable`). Two patterns iterate
  (`attZ_two_patterns`).
* **The pattern's crossover.** For `g(y) = y^{2k}` under a compact cutoff, the pattern energy
  `s E_s[g]` is `0` at `s → 0` (the pattern directions look flat under the prior) and `1/2k` as
  `s → ∞` (`tendsto_attEnergy_zero`, `tendsto_attEnergy_atTop`): the pattern is "learned" when
  `θ t`, the effective sample size devoted to it, crosses the scale of `g`. Together with the
  identity, `t E[L_θ] = λ_f + G_g(θ t)`.
* **Rigidity.** With a common minimiser, `min(θ, 1−θ)(f + g) ≤ L_θ ≤ max(θ, 1−θ)(f + g)`, so the
  partition function of `L_θ` is sandwiched between rescalings of that of `f + g`
  (`attZ_mixture_sandwich`), and its leading exponent and log multiplicity, in `Θ`-form, are the
  same for every `θ ∈ (0, 1)` (`mixture_isTheta`). Jumps of the local type along an attenuation
  path with a common minimiser can only occur where a mixture weight vanishes. Releasing a pattern
  lowers the partition function's decay: `Z_{f+g} ≤ Z_f` (`attZ_add_le`).
-/

open Real MeasureTheory Filter Topology Set Asymptotics

namespace Laplace.Multi

/-! ### Partition function and expectation with a cutoff -/

variable {Ω : Type*} [MeasureSpace Ω]

/-- Tempered partition function of `L` with cutoff `χ`. -/
noncomputable def attZ (L χ : Ω → ℝ) (t : ℝ) : ℝ := ∫ w, χ w * Real.exp (-(t * L w))

/-- Tempered numerator of the test `φ`. -/
noncomputable def attNum (L χ φ : Ω → ℝ) (t : ℝ) : ℝ := ∫ w, φ w * (χ w * Real.exp (-(t * L w)))

/-- Tempered expectation of `φ`. -/
noncomputable def attExp (L χ φ : Ω → ℝ) (t : ℝ) : ℝ := attNum L χ φ t / attZ L χ t

theorem attZ_scale (L χ : Ω → ℝ) (c t : ℝ) : attZ (fun w ↦ c * L w) χ t = attZ L χ (c * t) := by
  unfold attZ
  congr 1
  funext w
  ring_nf

/-! ### The separable attenuation identity -/

section Separable

variable {X Y : Type*} [MeasureSpace X] [MeasureSpace Y]
  [SigmaFinite (volume : Measure X)] [SigmaFinite (volume : Measure Y)]

/-- `Z(t) = Z_f(t) · Z_g(θ t)` for `L(x, y) = f x + θ g y` with a product cutoff. -/
theorem attZ_separable (f χf : X → ℝ) (g χg : Y → ℝ) (θ t : ℝ) :
    attZ (fun p : X × Y ↦ f p.1 + θ * g p.2) (fun p ↦ χf p.1 * χg p.2) t =
      attZ f χf t * attZ g χg (θ * t) := by
  unfold attZ
  have : (fun p : X × Y ↦ χf p.1 * χg p.2 * Real.exp (-(t * (f p.1 + θ * g p.2)))) =
      fun p ↦ (χf p.1 * Real.exp (-(t * f p.1))) * (χg p.2 * Real.exp (-(θ * t * g p.2))) := by
    funext p
    rw [show -(t * (f p.1 + θ * g p.2)) = -(t * f p.1) + -(θ * t * g p.2) by ring, Real.exp_add]
    ring
  rw [this, Measure.volume_eq_prod]
  exact integral_prod_mul (fun x ↦ χf x * Real.exp (-(t * f x)))
    (fun y ↦ χg y * Real.exp (-(θ * t * g y)))

/-- The energy numerator splits: `∫ (f + θ g) χ e^{-tL} = N_f(t) Z_g(θt) + θ Z_f(t) N_g(θt)`. -/
theorem attNum_separable (f χf : X → ℝ) (g χg : Y → ℝ) (θ t : ℝ)
    (hf : Integrable fun x ↦ χf x * Real.exp (-(t * f x)))
    (hff : Integrable fun x ↦ f x * (χf x * Real.exp (-(t * f x))))
    (hg : Integrable fun y ↦ χg y * Real.exp (-(θ * t * g y)))
    (hgg : Integrable fun y ↦ g y * (χg y * Real.exp (-(θ * t * g y)))) :
    attNum (fun p : X × Y ↦ f p.1 + θ * g p.2) (fun p ↦ χf p.1 * χg p.2)
        (fun p ↦ f p.1 + θ * g p.2) t =
      attNum f χf f t * attZ g χg (θ * t) + θ * (attZ f χf t * attNum g χg g (θ * t)) := by
  unfold attNum attZ
  have hsplit : (fun p : X × Y ↦ (f p.1 + θ * g p.2) *
      (χf p.1 * χg p.2 * Real.exp (-(t * (f p.1 + θ * g p.2))))) =
      fun p ↦ (f p.1 * (χf p.1 * Real.exp (-(t * f p.1)))) *
          (χg p.2 * Real.exp (-(θ * t * g p.2))) +
        θ * ((χf p.1 * Real.exp (-(t * f p.1))) *
          (g p.2 * (χg p.2 * Real.exp (-(θ * t * g p.2))))) := by
    funext p
    rw [show -(t * (f p.1 + θ * g p.2)) = -(t * f p.1) + -(θ * t * g p.2) by ring, Real.exp_add]
    ring
  rw [hsplit, Measure.volume_eq_prod]
  have h1 : Integrable (fun p : X × Y ↦ (f p.1 * (χf p.1 * Real.exp (-(t * f p.1)))) *
      (χg p.2 * Real.exp (-(θ * t * g p.2)))) (volume.prod volume) := hff.mul_prod hg
  have h2 : Integrable (fun p : X × Y ↦ θ * ((χf p.1 * Real.exp (-(t * f p.1))) *
      (g p.2 * (χg p.2 * Real.exp (-(θ * t * g p.2)))))) (volume.prod volume) :=
    (hf.mul_prod hgg).const_mul θ
  rw [integral_add h1 h2, integral_const_mul]
  have e1 := integral_prod_mul (μ := (volume : Measure X)) (ν := (volume : Measure Y))
    (fun x ↦ f x * (χf x * Real.exp (-(t * f x)))) (fun y ↦ χg y * Real.exp (-(θ * t * g y)))
  have e2 := integral_prod_mul (μ := (volume : Measure X)) (ν := (volume : Measure Y))
    (fun x ↦ χf x * Real.exp (-(t * f x))) (fun y ↦ g y * (χg y * Real.exp (-(θ * t * g y))))
  rw [e1, e2]

/-- **Attenuation is tempering**: `t E[L_θ] = t E_f[f](t) + (θ t) E_g[g](θ t)`. -/
theorem mul_attExp_separable (f χf : X → ℝ) (g χg : Y → ℝ) (θ t : ℝ)
    (hf : Integrable fun x ↦ χf x * Real.exp (-(t * f x)))
    (hff : Integrable fun x ↦ f x * (χf x * Real.exp (-(t * f x))))
    (hg : Integrable fun y ↦ χg y * Real.exp (-(θ * t * g y)))
    (hgg : Integrable fun y ↦ g y * (χg y * Real.exp (-(θ * t * g y))))
    (hZf : attZ f χf t ≠ 0) (hZg : attZ g χg (θ * t) ≠ 0) :
    t * attExp (fun p : X × Y ↦ f p.1 + θ * g p.2) (fun p ↦ χf p.1 * χg p.2)
        (fun p ↦ f p.1 + θ * g p.2) t =
      t * attExp f χf f t + (θ * t) * attExp g χg g (θ * t) := by
  unfold attExp
  rw [attNum_separable f χf g χg θ t hf hff hg hgg, attZ_separable]
  have hZg' : attZ g χg (t * θ) ≠ 0 := by rwa [mul_comm]
  field_simp

/-- Two patterns: `Z = Z_f(t) Z_{g₁}(θ₁ t) Z_{g₂}(θ₂ t)`. -/
theorem attZ_two_patterns {Y₂ : Type*} [MeasureSpace Y₂]
    [SigmaFinite (volume : Measure Y₂)]
    (f χf : X → ℝ) (g₁ χ₁ : Y → ℝ) (g₂ χ₂ : Y₂ → ℝ) (θ₁ θ₂ t : ℝ) :
    attZ (fun p : (X × Y) × Y₂ ↦ (f p.1.1 + θ₁ * g₁ p.1.2) + θ₂ * g₂ p.2)
        (fun p ↦ (χf p.1.1 * χ₁ p.1.2) * χ₂ p.2) t =
      attZ f χf t * attZ g₁ χ₁ (θ₁ * t) * attZ g₂ χ₂ (θ₂ * t) := by
  rw [attZ_separable (fun q : X × Y ↦ f q.1 + θ₁ * g₁ q.2) (fun q ↦ χf q.1 * χ₁ q.2) g₂ χ₂ θ₂ t,
    attZ_separable]

end Separable

/-! ### The pattern's crossover: `s E_s[y^{2k}]` from `0` to `1/2k` -/

section Crossover

/-- The pattern energy `s · E_s[g]` under the cutoff `χ`. -/
noncomputable def attEnergy (g χ : ℝ → ℝ) (s : ℝ) : ℝ := s * attExp g χ g s

/-- Standing hypotheses on a compactly supported cutoff seeing the origin. -/
structure Cutoff (χ : ℝ → ℝ) : Prop where
  cont : Continuous χ
  supp : HasCompactSupport χ
  nonneg : ∀ x, 0 ≤ χ x
  pos : 0 < χ 0

theorem Cutoff.exists_bound {χ : ℝ → ℝ} (hχ : Cutoff χ) : ∃ M, ∀ x, |χ x| ≤ M := by
  obtain ⟨M, hM⟩ := hχ.supp.isCompact_range hχ.cont |>.isBounded.exists_norm_le
  exact ⟨M, fun x ↦ by simpa using hM (χ x) ⟨x, rfl⟩⟩

/-- `∫ χ e^{-g} > 0` for a nonnegative cutoff positive at the origin. -/
theorem Cutoff.integral_mul_exp_pos {χ g : ℝ → ℝ} (hχ : Cutoff χ) (hg : Continuous g) (c : ℝ) :
    0 < ∫ x, χ x * Real.exp (-(c * g x)) := by
  have hint : Integrable fun x ↦ χ x * Real.exp (-(c * g x)) :=
    (hχ.cont.mul (by fun_prop)).integrable_of_hasCompactSupport hχ.supp.mul_right
  refine (integral_pos_iff_support_of_nonneg
    (fun x ↦ mul_nonneg (hχ.nonneg x) (Real.exp_pos _).le) hint).mpr ?_
  have hsub : Function.support χ ⊆ Function.support fun x ↦ χ x * Real.exp (-(c * g x)) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    exact mul_ne_zero hx (Real.exp_pos _).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  exact hχ.cont.isOpen_support.measure_pos volume ⟨0, hχ.pos.ne'⟩

/-- **Below the scale the pattern is invisible**: `s E_s[g] → 0` as `s → 0⁺`, for any continuous
`g ≥ 0`. -/
theorem tendsto_attEnergy_zero {g χ : ℝ → ℝ} (hχ : Cutoff χ) (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) :
    Tendsto (attEnergy g χ) (𝓝[>] 0) (𝓝 0) := by
  set N₀ : ℝ := ∫ x, g x * χ x with hN₀
  set D₁ : ℝ := ∫ x, χ x * Real.exp (-(1 * g x)) with hD₁
  have hD₁pos : 0 < D₁ := hχ.integral_mul_exp_pos hg 1
  have hN₀nn : 0 ≤ N₀ := integral_nonneg fun x ↦ mul_nonneg (hg0 x) (hχ.nonneg x)
  have hnn : ∀ s, 0 < s → 0 ≤ attEnergy g χ s := by
    intro s hs
    have hDs : 0 < attZ g χ s := hχ.integral_mul_exp_pos hg s
    have hNs_nn : 0 ≤ attNum g χ g s :=
      integral_nonneg fun x ↦ mul_nonneg (hg0 x) (mul_nonneg (hχ.nonneg x) (Real.exp_pos _).le)
    exact mul_nonneg hs.le (div_nonneg hNs_nn hDs.le)
  have hbound : ∀ s, 0 < s → s ≤ 1 → attEnergy g χ s ≤ s * (N₀ / D₁) := by
    intro s hs hs1
    have hDs : 0 < attZ g χ s := hχ.integral_mul_exp_pos hg s
    have hNint : Integrable fun x ↦ g x * χ x :=
      (hg.mul hχ.cont).integrable_of_hasCompactSupport hχ.supp.mul_left
    have hNs_nn : 0 ≤ attNum g χ g s :=
      integral_nonneg fun x ↦ mul_nonneg (hg0 x) (mul_nonneg (hχ.nonneg x) (Real.exp_pos _).le)
    have hNs_le : attNum g χ g s ≤ N₀ := by
      unfold attNum
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦
        mul_nonneg (hg0 x) (mul_nonneg (hχ.nonneg x) (Real.exp_pos _).le)) hNint
        (Filter.Eventually.of_forall fun x ↦ ?_)
      have hexp : Real.exp (-(s * g x)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := mul_nonneg hs.le (hg0 x)
        linarith
      calc g x * (χ x * Real.exp (-(s * g x))) ≤ g x * (χ x * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (hχ.nonneg x)) (hg0 x)
        _ = g x * χ x := by ring
    have hDs_ge : D₁ ≤ attZ g χ s := by
      unfold attZ
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦
        mul_nonneg (hχ.nonneg x) (Real.exp_pos _).le)
        ((hχ.cont.mul (by fun_prop)).integrable_of_hasCompactSupport hχ.supp.mul_right)
        (Filter.Eventually.of_forall fun x ↦ ?_)
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hχ.nonneg x)
      have := mul_le_mul_of_nonneg_right hs1 (hg0 x)
      linarith
    unfold attEnergy attExp
    refine mul_le_mul_of_nonneg_left ?_ hs.le
    exact div_le_div₀ hN₀nn hNs_le hD₁pos hDs_ge
  have hlim : Tendsto (fun s : ℝ ↦ s * (N₀ / D₁)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ ↦ s * (N₀ / D₁)) (𝓝[>] 0) (𝓝 (0 * (N₀ / D₁))) :=
      ((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left nhdsWithin_le_nhds).mul_const _
    rwa [zero_mul] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact hnn s hs
  · have h1 : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
    filter_upwards [self_mem_nhdsWithin, h1] with s hs hs1
    exact hbound s hs (le_of_lt hs1)


/-! #### Above the scale: `s E_s[x^{2k}] → 1/2k` -/

/-- Substitution `x = s^{-1/2k} u` in a cutoff moment integral. -/
theorem rpow_mul_integral_eq (χ : ℝ → ℝ) (k m : ℕ) (hk : 1 ≤ k) {s : ℝ} (hs : 0 < s) :
    s ^ (((m : ℝ) + 1) / (2 * k)) * ∫ x, χ x * |x| ^ m * Real.exp (-(s * x ^ (2 * k))) =
      ∫ u, χ (s ^ (-(1 / (2 * k : ℝ))) * u) * |u| ^ m * Real.exp (-u ^ (2 * k)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set q : ℝ := s ^ (-(1 / (2 * k : ℝ))) with hq
  have hqpos : 0 < q := Real.rpow_pos_of_pos hs _
  have hq2k : s * q ^ (2 * k) = 1 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    push_cast
    rw [show -(1 / (2 * (k : ℝ))) * (2 * k) = -1 by field_simp, Real.rpow_neg_one,
      mul_inv_cancel₀ hs.ne']
  have hqm : s ^ (((m : ℝ) + 1) / (2 * k)) * q ^ (m + 1) = 1 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hs.le, ← Real.rpow_add hs]
    push_cast
    rw [show ((m : ℝ) + 1) / (2 * k) + -(1 / (2 * k)) * ((m : ℝ) + 1) = 0 by ring, Real.rpow_zero]
  have hcomp := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ χ x * |x| ^ m * Real.exp (-(s * x ^ (2 * k)))) q
  rw [abs_inv, abs_of_pos hqpos, smul_eq_mul] at hcomp
  have hpt : ∀ u : ℝ, χ (q * u) * |q * u| ^ m * Real.exp (-(s * (q * u) ^ (2 * k))) =
      q ^ m * (χ (q * u) * |u| ^ m * Real.exp (-u ^ (2 * k))) := by
    intro u
    rw [abs_mul, abs_of_pos hqpos, mul_pow, mul_pow,
      show s * (q ^ (2 * k) * u ^ (2 * k)) = (s * q ^ (2 * k)) * u ^ (2 * k) by ring, hq2k, one_mul]
    ring
  simp only [hpt, integral_const_mul] at hcomp
  have hI : (∫ x, χ x * |x| ^ m * Real.exp (-(s * x ^ (2 * k)))) =
      q ^ (m + 1) * ∫ u, χ (q * u) * |u| ^ m * Real.exp (-u ^ (2 * k)) := by
    have hF : (∫ x, χ x * |x| ^ m * Real.exp (-(s * x ^ (2 * k)))) =
        q * (q⁻¹ * ∫ x, χ x * |x| ^ m * Real.exp (-(s * x ^ (2 * k)))) := by
      rw [← mul_assoc, mul_inv_cancel₀ hqpos.ne', one_mul]
    rw [hF, ← hcomp, pow_succ]
    ring
  rw [hI, ← mul_assoc, hqm, one_mul]

/-- Dominated convergence for the rescaled cutoff moment. -/
theorem tendsto_scaled_cutoff {χ : ℝ → ℝ} (hχ : Cutoff χ) (k m : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun s : ℝ ↦ ∫ u, χ (s ^ (-(1 / (2 * k : ℝ))) * u) * |u| ^ m * Real.exp (-u ^ (2 * k)))
      atTop (𝓝 (χ 0 * agmom k m)) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hlim : (∫ u : ℝ, χ 0 * |u| ^ m * Real.exp (-u ^ (2 * k))) = χ 0 * agmom k m := by
    unfold agmom
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  rw [← hlim]
  have hq : Tendsto (fun s : ℝ ↦ s ^ (-(1 / (2 * k : ℝ)))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by positivity)
  have hχc := hχ.cont
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u ↦ M * (|u| ^ m * Real.exp (-(1 * u ^ (2 * k)))))
    (Filter.Eventually.of_forall fun s ↦ (by fun_prop : Continuous fun u : ℝ ↦
      χ (s ^ (-(1 / (2 * k : ℝ))) * u) * |u| ^ m * Real.exp (-u ^ (2 * k))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun s ↦ Filter.Eventually.of_forall fun u ↦ ?_)
    ((integrable_abs_pow_mul_exp_neg_mul_pow one_pos k hk m).const_mul M)
    (Filter.Eventually.of_forall fun u ↦ ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_abs, Real.abs_exp, one_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
  · have h0 : Tendsto (fun s : ℝ ↦ s ^ (-(1 / (2 * k : ℝ))) * u) atTop (𝓝 0) := by
      simpa using hq.mul_const u
    exact (((hχc.tendsto 0).comp h0).mul_const _).mul_const _

/-- **Above the scale the pattern's exponent is read off**: `s E_s[x^{2k}] → 1/2k` as `s → ∞`. -/
theorem tendsto_attEnergy_atTop {χ : ℝ → ℝ} (hχ : Cutoff χ) (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (attEnergy (fun x ↦ x ^ (2 * k)) χ) atTop (𝓝 (1 / (2 * k))) := by
  have hN := tendsto_scaled_cutoff hχ k (2 * k) hk
  have hD := tendsto_scaled_cutoff hχ k 0 hk
  have hpos : χ 0 * agmom k 0 ≠ 0 := (mul_pos hχ.pos (agmom_pos k hk 0)).ne'
  have hratio := hN.div hD hpos
  have hval : χ 0 * agmom k (2 * k) / (χ 0 * agmom k 0) = 1 / (2 * k) := by
    rw [mul_div_mul_left _ _ hχ.pos.ne']
    have h1 : agmom k (2 * k) = gmom k (2 * k) := by
      unfold agmom gmom
      congr 1
      funext u
      rw [pow_mul, sq_abs, ← pow_mul]
    have h0 : agmom k 0 = gmom k 0 := by
      unfold agmom gmom
      simp
    rw [h1, h0, gmom_two_k_div_zero k hk]
  rw [hval] at hratio
  refine hratio.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp only [Pi.div_apply]
  rw [← rpow_mul_integral_eq χ k (2 * k) hk hs, ← rpow_mul_integral_eq χ k 0 hk hs]
  have e1 : (fun x : ℝ ↦ χ x * |x| ^ (2 * k) * Real.exp (-(s * x ^ (2 * k)))) =
      fun x ↦ x ^ (2 * k) * (χ x * Real.exp (-(s * x ^ (2 * k)))) := by
    funext x
    rw [pow_mul, sq_abs, ← pow_mul]
    ring
  have e0 : (fun x : ℝ ↦ χ x * |x| ^ 0 * Real.exp (-(s * x ^ (2 * k)))) =
      fun x ↦ χ x * Real.exp (-(s * x ^ (2 * k))) := by
    funext x
    simp
  have hexp : s ^ ((((2 * k : ℕ) : ℝ) + 1) / (2 * k)) =
      s * s ^ ((((0 : ℕ) : ℝ) + 1) / (2 * k)) := by
    push_cast
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [show (2 * (k : ℝ) + 1) / (2 * k) = 1 + (0 + 1) / (2 * k) by field_simp; ring,
      Real.rpow_add hs, Real.rpow_one]
  have hZpos : 0 < ∫ x, χ x * Real.exp (-(s * x ^ (2 * k))) :=
    hχ.integral_mul_exp_pos (by fun_prop) s
  have hr : s ^ ((((0 : ℕ) : ℝ) + 1) / (2 * k)) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
  rw [e1, e0, hexp]
  unfold attEnergy attExp attNum attZ
  field_simp

end Crossover

/-! ### Rigidity along a mixture path with a common minimiser -/

section Rigidity

variable {d : ℕ}

theorem integrable_cutoff_mul_exp {χ L : EuclidD d → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (hL : Continuous L) (t : ℝ) :
    Integrable fun w ↦ χ w * Real.exp (-(t * L w)) :=
  (hχc.mul (by fun_prop)).integrable_of_hasCompactSupport hχs.mul_right

theorem attZ_nonneg {L χ : EuclidD d → ℝ} (hχ : ∀ w, 0 ≤ χ w) (t : ℝ) : 0 ≤ attZ L χ t :=
  integral_nonneg fun w ↦ mul_nonneg (hχ w) (Real.exp_pos _).le

/-- A larger loss has a smaller partition function. -/
theorem attZ_mono {L₁ L₂ χ : EuclidD d → ℝ} (hχ : ∀ w, 0 ≤ χ w) (hL : ∀ w, L₁ w ≤ L₂ w) {t : ℝ}
    (ht : 0 ≤ t) (hint : Integrable fun w ↦ χ w * Real.exp (-(t * L₁ w))) :
    attZ L₂ χ t ≤ attZ L₁ χ t := by
  unfold attZ
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w ↦
    mul_nonneg (hχ w) (Real.exp_pos _).le) hint (Filter.Eventually.of_forall fun w ↦ ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hχ w)
  have := mul_le_mul_of_nonneg_left (hL w) ht
  linarith

/-- **Releasing a pattern lowers the decay of the partition function**: `Z_{f+g} ≤ Z_f`. -/
theorem attZ_add_le {f g χ : EuclidD d → ℝ} (hχ : ∀ w, 0 ≤ χ w) (hg : ∀ w, 0 ≤ g w) {t : ℝ}
    (ht : 0 ≤ t) (hint : Integrable fun w ↦ χ w * Real.exp (-(t * f w))) :
    attZ (fun w ↦ f w + g w) χ t ≤ attZ f χ t :=
  attZ_mono hχ (fun w ↦ by linarith [hg w]) ht hint

/-- **The mixture sandwich**:
`Z_{f+g}(max(θ,1−θ) t) ≤ Z_{(1−θ)f+θg}(t) ≤ Z_{f+g}(min(θ,1−θ) t)`. -/
theorem attZ_mixture_sandwich {f g χ : EuclidD d → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (hχ : ∀ w, 0 ≤ χ w) (hfc : Continuous f) (hgc : Continuous g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w) (θ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    attZ (fun w ↦ f w + g w) χ (max θ (1 - θ) * t) ≤
        attZ (fun w ↦ (1 - θ) * f w + θ * g w) χ t ∧
      attZ (fun w ↦ (1 - θ) * f w + θ * g w) χ t ≤
        attZ (fun w ↦ f w + g w) χ (min θ (1 - θ) * t) := by
  constructor
  · rw [← attZ_scale]
    refine attZ_mono hχ (fun w ↦ ?_) ht
      (integrable_cutoff_mul_exp hχc hχs (by fun_prop) t)
    have h1 : (1 - θ) * f w ≤ max θ (1 - θ) * f w :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (hf w)
    have h2 : θ * g w ≤ max θ (1 - θ) * g w :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (hg w)
    linarith
  · rw [← attZ_scale]
    refine attZ_mono hχ (fun w ↦ ?_) ht
      (integrable_cutoff_mul_exp hχc hχs (by fun_prop) t)
    have h1 : min θ (1 - θ) * f w ≤ (1 - θ) * f w :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (hf w)
    have h2 : min θ (1 - θ) * g w ≤ θ * g w :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (hg w)
    linarith

/-- Rescaling the argument by a positive constant preserves `Θ(t^{-λ} log^p t)`. -/
theorem isTheta_comp_const_mul {Z : ℝ → ℝ} {lam : ℝ} {p : ℕ}
    (hZ : Z =Θ[atTop] fun t ↦ t ^ (-lam) * Real.log t ^ p) {c : ℝ} (hc : 0 < c) :
    (fun t ↦ Z (c * t)) =Θ[atTop] fun t ↦ t ^ (-lam) * Real.log t ^ p := by
  have hct : Tendsto (fun t : ℝ ↦ c * t) atTop atTop := Tendsto.const_mul_atTop hc tendsto_id
  have h1 : (fun t ↦ Z (c * t)) =Θ[atTop] fun t ↦ (c * t) ^ (-lam) * Real.log (c * t) ^ p :=
    ⟨hZ.1.comp_tendsto hct, hZ.2.comp_tendsto hct⟩
  refine h1.trans (IsTheta.mul ?_ ?_)
  · have heq : (fun t : ℝ ↦ (c * t) ^ (-lam)) =ᶠ[atTop] fun t ↦ c ^ (-lam) * t ^ (-lam) := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [Real.mul_rpow hc.le ht.le]
    refine heq.isTheta.trans ?_
    exact (isTheta_const_mul_left (Real.rpow_pos_of_pos hc _).ne').mpr isTheta_rfl
  · refine IsTheta.pow ?_ p
    refine (isEquivalent_of_tendsto_one ?_).isTheta
    · have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
      have h2 : Tendsto (fun t : ℝ ↦ Real.log c / Real.log t + 1) atTop (𝓝 (0 + 1)) :=
        (tendsto_const_nhds.div_atTop hlog).add tendsto_const_nhds
      rw [zero_add] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with t ht
      have hlt : Real.log t ≠ 0 := (Real.log_pos ht).ne'
      simp only [Pi.div_apply]
      rw [Real.log_mul hc.ne' (by linarith), add_div, div_self hlt]

/-- A function sandwiched between two `Θ(T)` functions is `Θ(T)`. -/
theorem isTheta_of_sandwich {Z₁ Z₂ Z₃ T : ℝ → ℝ} (hnn : ∀ᶠ t in atTop, 0 ≤ Z₁ t)
    (hlo : ∀ᶠ t in atTop, Z₁ t ≤ Z₂ t) (hhi : ∀ᶠ t in atTop, Z₂ t ≤ Z₃ t)
    (h₁ : Z₁ =Θ[atTop] T) (h₃ : Z₃ =Θ[atTop] T) : Z₂ =Θ[atTop] T := by
  constructor
  · refine (IsBigO.of_bound' ?_).trans h₃.1
    filter_upwards [hnn, hlo, hhi] with t h0 h1 h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h0.trans h1),
      abs_of_nonneg ((h0.trans h1).trans h2)]
    exact h2
  · refine h₁.2.trans (IsBigO.of_bound' ?_)
    filter_upwards [hnn, hlo] with t h0 h1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (h0.trans h1)]
    exact h1

/-- **Rigidity of the local type along a mixture with a common minimiser.** If
`Z_{f+g}(t) = Θ(t^{-λ} log^p t)` then so is `Z_{(1−θ)f+θg}(t)` for every `θ ∈ (0, 1)`: the leading
exponent and log multiplicity cannot jump in the interior of the mixture interval. -/
theorem mixture_isTheta {f g χ : EuclidD d → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχ : ∀ w, 0 ≤ χ w) (hfc : Continuous f) (hgc : Continuous g) (hf : ∀ w, 0 ≤ f w)
    (hg : ∀ w, 0 ≤ g w) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {lam : ℝ} {p : ℕ}
    (hZ : attZ (fun w ↦ f w + g w) χ =Θ[atTop] fun t ↦ t ^ (-lam) * Real.log t ^ p) :
    attZ (fun w ↦ (1 - θ) * f w + θ * g w) χ =Θ[atTop]
      fun t ↦ t ^ (-lam) * Real.log t ^ p := by
  have hmin : 0 < min θ (1 - θ) := lt_min hθ0 (by linarith)
  have hmax : 0 < max θ (1 - θ) := lt_of_lt_of_le hθ0 (le_max_left _ _)
  refine isTheta_of_sandwich (Z₁ := fun t ↦ attZ (fun w ↦ f w + g w) χ (max θ (1 - θ) * t))
    (Z₃ := fun t ↦ attZ (fun w ↦ f w + g w) χ (min θ (1 - θ) * t))
    (Filter.Eventually.of_forall fun t ↦ attZ_nonneg hχ _) ?_ ?_
    (isTheta_comp_const_mul hZ hmax) (isTheta_comp_const_mul hZ hmin)
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact (attZ_mixture_sandwich hχc hχs hχ hfc hgc hf hg θ ht).1
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact (attZ_mixture_sandwich hχc hχs hχ hfc hgc hf hg θ ht).2

end Rigidity

end Laplace.Multi
