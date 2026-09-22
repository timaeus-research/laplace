/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.RelativeChartLeading

/-!
# The local model of a chamber wall: a unit degenerating to a monomial

In a relative chart the loss is `a(x, s) x^{2k}` with a unit `a`. At a wall of the chamber
decomposition the unit loses its uniform lower bound; the simplest way is
`a(x, s) = ε(s) + x^{2m}` with `ε(s) → 0` at the wall. Off the wall the chart has type
`e₂ = (h + 1)/2k`; on the wall the loss is `x^{2(k+m)}` with type `e₁ = (h + 1)/2(k + m)`. The toy
`x⁴ + u²x²` of `ToyCrossover` is `k = m = 1`, `h = 0`, `ε = u²`.

* The energy statistic of the chart is EXACTLY a function of the combined variable
  `s = ε · t^{m/(k+m)}` (`wallEnergy_eq_wallCross`): `t E_{ε,t}[L] = G_{k,m,h}(ε t^{m/(k+m)})` with
  `G(s) = ∫ (s u^{2k} + u^{2(k+m)}) |u|^h e^{-(s u^{2k} + u^{2(k+m)})} / ∫ |u|^h e^{-(…)}`.
* `G(0) = (h+1)/2(k+m)` (`wallCross_zero`) and `G(s) → (h+1)/2k` as `s → ∞`
  (`tendsto_wallCross_atTop`): the energy crosses from the wall type to the chamber type.

The combined variable is universal for this mechanism; the shape `G` is not (it depends on the
full expansion of the degenerating unit), which is what the numerical zoo of germbij_slop S10 shows.
-/

open Real MeasureTheory Filter Topology Set

namespace Laplace.Multi

/-! ### Generalised Gaussian moments in Gamma form -/

theorem abs_pow_even (u : ℝ) (j : ℕ) : |u| ^ (2 * j) = u ^ (2 * j) := by
  rw [pow_mul, pow_mul, sq_abs]

/-- `∫ |u|^h e^{-u^{2k}} du = Γ((h+1)/2k)/k`. -/
theorem agmom_eq_Gamma (k : ℕ) (hk : 1 ≤ k) (h : ℕ) :
    agmom k h = Real.Gamma (((h : ℝ) + 1) / (2 * k)) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold agmom
  set F : ℝ → ℝ := fun v ↦ v ^ h * Real.exp (-v ^ (2 * k)) with hF
  have heven : (fun u : ℝ ↦ |u| ^ h * Real.exp (-u ^ (2 * k))) = fun u ↦ F |u| := by
    funext u
    simp only [hF]
    rw [abs_pow_even]
  rw [heven, integral_comp_abs (f := F)]
  simp only [hF]
  have hpt : ∀ v ∈ Ioi (0 : ℝ), v ^ h * Real.exp (-v ^ (2 * k)) =
      v ^ (h : ℝ) * Real.exp (-v ^ ((2 * k : ℕ) : ℝ)) := fun v _ => by
    rw [Real.rpow_natCast, Real.rpow_natCast]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  rw [integral_rpow_mul_exp_neg_rpow (by positivity) (by
    have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    linarith)]
  push_cast
  field_simp

/-- The shift identity `∫ |u|^{h+2k} e^{-u^{2k}} / ∫ |u|^h e^{-u^{2k}} = (h+1)/2k`. -/
theorem agmom_shift_div (k : ℕ) (hk : 1 ≤ k) (h : ℕ) :
    agmom k (h + 2 * k) / agmom k h = ((h : ℝ) + 1) / (2 * k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [agmom_eq_Gamma k hk, agmom_eq_Gamma k hk]
  have hx : (0 : ℝ) < ((h : ℝ) + 1) / (2 * k) := by positivity
  have hshift : (((h + 2 * k : ℕ) : ℝ) + 1) / (2 * k) = ((h : ℝ) + 1) / (2 * k) + 1 := by
    push_cast
    field_simp
    ring
  rw [hshift, Real.Gamma_add_one hx.ne']
  have hG : 0 < Real.Gamma (((h : ℝ) + 1) / (2 * k)) := Real.Gamma_pos_of_pos hx
  field_simp

/-! ### The wall crossover function -/

/-- The wall weight `|u|^h e^{-(s u^{2k} + u^{2(k+m)})}`. -/
noncomputable def wallW (k m h : ℕ) (s u : ℝ) : ℝ :=
  |u| ^ h * Real.exp (-(s * u ^ (2 * k) + u ^ (2 * (k + m))))

/-- The crossover function `G(s) = E_s[s u^{2k} + u^{2(k+m)}]`. -/
noncomputable def wallCross (k m h : ℕ) (s : ℝ) : ℝ :=
  (∫ u, (s * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h s u) / ∫ u, wallW k m h s u

theorem even_pow_nonneg (u : ℝ) (j : ℕ) : 0 ≤ u ^ (2 * j) := by
  rw [pow_mul]
  positivity

theorem wallW_pos (k m h : ℕ) (s : ℝ) {u : ℝ} (hu : u ≠ 0) : 0 < wallW k m h s u :=
  mul_pos (pow_pos (abs_pos.mpr hu) _) (Real.exp_pos _)

theorem wallW_nonneg (k m h : ℕ) (s u : ℝ) : 0 ≤ wallW k m h s u :=
  mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le

theorem wallW_le {k m h : ℕ} {s : ℝ} (hs : 0 ≤ s) (u : ℝ) :
    wallW k m h s u ≤ |u| ^ h * Real.exp (-(1 * u ^ (2 * (k + m)))) := by
  unfold wallW
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg (abs_nonneg _) _)
  have := mul_nonneg hs (even_pow_nonneg u k)
  linarith

theorem integrable_abs_pow_mul_wallW (k m h j : ℕ) (hn : 1 ≤ k + m) {s : ℝ} (hs : 0 ≤ s) :
    Integrable fun u ↦ |u| ^ j * wallW k m h s u := by
  refine (integrable_abs_pow_mul_exp_neg_mul_pow one_pos (k + m) hn (h + j)).mono'
    (by unfold wallW; fun_prop) (Filter.Eventually.of_forall fun u ↦ ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) (wallW_nonneg _ _ _ _ _)), pow_add]
  calc |u| ^ j * wallW k m h s u ≤ |u| ^ j * (|u| ^ h * Real.exp (-(1 * u ^ (2 * (k + m))))) :=
        mul_le_mul_of_nonneg_left (wallW_le hs u) (pow_nonneg (abs_nonneg _) _)
    _ = |u| ^ h * |u| ^ j * Real.exp (-(1 * u ^ (2 * (k + m)))) := by ring

theorem integral_wallW_pos (k m h : ℕ) (hn : 1 ≤ k + m) {s : ℝ} (hs : 0 ≤ s) :
    0 < ∫ u, wallW k m h s u := by
  have hi := integrable_abs_pow_mul_wallW k m h 0 hn hs
  simp only [pow_zero, one_mul] at hi
  refine (integral_pos_iff_support_of_nonneg (wallW_nonneg k m h s) hi).mpr ?_
  have hsub : Ioi (0 : ℝ) ⊆ Function.support (wallW k m h s) := fun u hu ↦
    (wallW_pos k m h s (ne_of_gt hu)).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  simp [Real.volume_Ioi]

/-- **At the wall** the energy is the wall type `(h+1)/2(k+m)`. -/
theorem wallCross_zero (k m h : ℕ) (hn : 1 ≤ k + m) :
    wallCross k m h 0 = ((h : ℝ) + 1) / (2 * (k + m)) := by
  have hnum : (∫ u, (0 * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h 0 u) =
      agmom (k + m) (h + 2 * (k + m)) := by
    unfold agmom wallW
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    simp only [zero_mul, zero_add]
    rw [pow_add, abs_pow_even]
    ring
  have hden : (∫ u, wallW k m h 0 u) = agmom (k + m) h := by
    unfold agmom wallW
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    simp
  unfold wallCross
  rw [hnum, hden, agmom_shift_div (k + m) hn h]
  push_cast
  ring

/-! ### Above the wall: `G(s) → (h+1)/2k` -/

/-- The small parameter of the rescaled form, `δ = s^{-(k+m)/k}`. -/
noncomputable def wallDelta (k m : ℕ) (s : ℝ) : ℝ := s ^ (-(((k : ℝ) + m) / k))

theorem tendsto_wallDelta (k m : ℕ) (hk : 1 ≤ k) : Tendsto (wallDelta k m) atTop (𝓝 0) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  exact tendsto_rpow_neg_atTop (by positivity)

/-- With `u = s^{-1/2k} v`: `G(s)` is the energy of `v^{2k} + δ v^{2(k+m)}` under
`|v|^h e^{-(v^{2k} + δ v^{2(k+m)})}`, `δ = s^{-(k+m)/k}`. -/
theorem wallCross_eq_rescaled (k m h : ℕ) (hk : 1 ≤ k) {s : ℝ} (hs : 0 < s) :
    wallCross k m h s =
      (∫ v, (v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m))) *
          (|v| ^ h * Real.exp (-(v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m)))))) /
        ∫ v, |v| ^ h * Real.exp (-(v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m)))) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set c : ℝ := s ^ (-(1 / (2 * k : ℝ))) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hs _
  have hc2k : s * c ^ (2 * k) = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    push_cast
    rw [show -(1 / (2 * (k : ℝ))) * (2 * k) = -1 by field_simp, Real.rpow_neg_one,
      mul_inv_cancel₀ hs.ne']
  have hc2n : c ^ (2 * (k + m)) = wallDelta k m s := by
    rw [hc, wallDelta, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    push_cast
    congr 1
    field_simp
  have hpt : ∀ v : ℝ, s * (c * v) ^ (2 * k) + (c * v) ^ (2 * (k + m)) =
      v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m)) := by
    intro v
    rw [mul_pow, mul_pow, ← mul_assoc, hc2k, one_mul, hc2n]
  have hW : ∀ v : ℝ, wallW k m h s (c * v) =
      c ^ h * (|v| ^ h * Real.exp (-(v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m))))) := by
    intro v
    unfold wallW
    rw [hpt, abs_mul, abs_of_pos hcpos, mul_pow]
    ring
  have hn := Measure.integral_comp_mul_left
    (fun u : ℝ ↦ (s * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h s u) c
  have hd := Measure.integral_comp_mul_left (fun u : ℝ ↦ wallW k m h s u) c
  rw [abs_inv, abs_of_pos hcpos, smul_eq_mul] at hn hd
  simp only [hpt, hW] at hn hd
  have hn' : (∫ u, (s * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h s u) =
      c * ∫ v, (v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m))) *
        (c ^ h * (|v| ^ h * Real.exp (-(v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m)))))) := by
    rw [hn, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  have hd' : (∫ u, wallW k m h s u) = c * ∫ v,
      c ^ h * (|v| ^ h * Real.exp (-(v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m))))) := by
    rw [hd, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  unfold wallCross
  rw [hn', hd']
  have e1 : (fun v : ℝ ↦ (v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m))) *
      (c ^ h * (|v| ^ h * Real.exp (-(v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m))))))) =
      fun v ↦ c ^ h * ((v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m))) *
        (|v| ^ h * Real.exp (-(v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m)))))) := by
    funext v
    ring
  rw [e1, integral_const_mul, integral_const_mul, mul_div_mul_left _ _ hcpos.ne',
    mul_div_mul_left _ _ (pow_ne_zero _ hcpos.ne')]

/-- **Above the wall** the energy tends to the chamber type `(h+1)/2k`. -/
theorem tendsto_wallCross_atTop (k m h : ℕ) (hk : 1 ≤ k) :
    Tendsto (wallCross k m h) atTop (𝓝 (((h : ℝ) + 1) / (2 * k))) := by
  have hlim : (∫ v : ℝ, v ^ (2 * k) * (|v| ^ h * Real.exp (-v ^ (2 * k)))) /
      (∫ v : ℝ, |v| ^ h * Real.exp (-v ^ (2 * k))) = ((h : ℝ) + 1) / (2 * k) := by
    rw [← agmom_shift_div k hk h]
    unfold agmom
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
    simp only
    rw [pow_add, abs_pow_even]
    ring
  have hI0 := integrable_abs_pow_mul_exp_neg_mul_pow one_pos k hk h
  have hI1 := integrable_abs_pow_mul_exp_neg_mul_pow one_pos k hk (h + 2 * k)
  have hI2 := integrable_abs_pow_mul_exp_neg_mul_pow one_pos k hk (h + 2 * (k + m))
  simp only [one_mul] at hI0 hI1 hI2
  have hdom : Integrable fun v : ℝ ↦
      (v ^ (2 * k) + v ^ (2 * (k + m))) * (|v| ^ h * Real.exp (-v ^ (2 * k))) := by
    refine (hI1.add hI2).congr (Filter.Eventually.of_forall fun v ↦ ?_)
    simp only [Pi.add_apply]
    rw [pow_add, pow_add, abs_pow_even, abs_pow_even]
    ring
  have hδ := tendsto_wallDelta k m hk
  have hev : ∀ᶠ s in atTop, 0 ≤ wallDelta k m s ∧ wallDelta k m s ≤ 1 := by
    filter_upwards [eventually_gt_atTop 0, hδ.eventually (eventually_le_nhds zero_lt_one)]
      with s hs h1
    exact ⟨(Real.rpow_pos_of_pos hs _).le, h1⟩
  have hpt : ∀ v : ℝ, Tendsto (fun s ↦ v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m))) atTop
      (𝓝 (v ^ (2 * k))) := by
    intro v
    have := (hδ.mul_const (v ^ (2 * (k + m)))).const_add (v ^ (2 * k))
    simpa using this
  have hexp : ∀ v : ℝ, Tendsto (fun s ↦
      |v| ^ h * Real.exp (-(v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m))))) atTop
      (𝓝 (|v| ^ h * Real.exp (-v ^ (2 * k)))) := fun v ↦
    ((Real.continuous_exp.tendsto _).comp (hpt v).neg).const_mul _
  have hbound : ∀ s, 0 ≤ wallDelta k m s → wallDelta k m s ≤ 1 → ∀ v : ℝ,
      |v| ^ h * Real.exp (-(v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m)))) ≤
        |v| ^ h * Real.exp (-v ^ (2 * k)) := by
    intro s hs0 hs1 v
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg (abs_nonneg _) _)
    have := mul_nonneg hs0 (even_pow_nonneg v (k + m))
    linarith
  have hnum : Tendsto (fun s ↦ ∫ v, (v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m))) *
      (|v| ^ h * Real.exp (-(v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m)))))) atTop
      (𝓝 (∫ v, v ^ (2 * k) * (|v| ^ h * Real.exp (-v ^ (2 * k))))) := by
    refine tendsto_integral_filter_of_dominated_convergence _
      (Filter.Eventually.of_forall fun s ↦ by fun_prop) ?_ hdom
      (Filter.Eventually.of_forall fun v ↦ (hpt v).mul (hexp v))
    filter_upwards [hev] with s hs
    exact Filter.Eventually.of_forall fun v ↦ by
      rw [Real.norm_eq_abs]
      have h2k := even_pow_nonneg v k
      have h2n := even_pow_nonneg v (k + m)
      have hδv : 0 ≤ wallDelta k m s * v ^ (2 * (k + m)) := mul_nonneg hs.1 h2n
      have hδv' : wallDelta k m s * v ^ (2 * (k + m)) ≤ v ^ (2 * (k + m)) := by
        calc wallDelta k m s * v ^ (2 * (k + m)) ≤ 1 * v ^ (2 * (k + m)) :=
              mul_le_mul_of_nonneg_right hs.2 h2n
          _ = _ := one_mul _
      rw [abs_of_nonneg (mul_nonneg (by linarith)
        (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le))]
      exact mul_le_mul (by linarith) (hbound s hs.1 hs.2 v)
        (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le) (by linarith)
  have hden : Tendsto (fun s ↦ ∫ v,
      |v| ^ h * Real.exp (-(v ^ (2 * k) + wallDelta k m s * v ^ (2 * (k + m))))) atTop
      (𝓝 (∫ v, |v| ^ h * Real.exp (-v ^ (2 * k)))) := by
    refine tendsto_integral_filter_of_dominated_convergence _
      (Filter.Eventually.of_forall fun s ↦ by fun_prop) ?_ hI0
      (Filter.Eventually.of_forall fun v ↦ hexp v)
    filter_upwards [hev] with s hs
    exact Filter.Eventually.of_forall fun v ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _)
        (Real.exp_pos _).le)]
      exact hbound s hs.1 hs.2 v
  have hden0 : (∫ v : ℝ, |v| ^ h * Real.exp (-v ^ (2 * k))) ≠ 0 := (agmom_pos k hk h).ne'
  have := hnum.div hden hden0
  rw [hlim] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  simp only [Pi.div_apply]
  rw [wallCross_eq_rescaled k m h hk hs]

/-! ### The chart energy is exactly a function of the combined variable -/

/-- The energy statistic `t E_{ε,t}[L_ε]` of the chart `L_ε(x) = (ε + x^{2m}) x^{2k}` with Jacobian
weight `|x|^h`. -/
noncomputable def wallEnergy (k m h : ℕ) (ε t : ℝ) : ℝ :=
  t * ((∫ x, (ε + x ^ (2 * m)) * x ^ (2 * k) *
      (|x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k)))))) /
    ∫ x, |x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k)))))

/-- **Scaling collapse at a wall**: `t E_{ε,t}[L_ε] = G_{k,m,h}(ε t^{m/(k+m)})`. -/
theorem wallEnergy_eq_wallCross (k m h : ℕ) (hn : 1 ≤ k + m) (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    wallEnergy k m h ε t = wallCross k m h (ε * t ^ ((m : ℝ) / (k + m))) := by
  have hn' : (0 : ℝ) < (k : ℝ) + m := by exact_mod_cast hn
  set c : ℝ := t ^ (-(1 / (2 * ((k : ℝ) + m)))) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hc2n : t * c ^ (2 * (k + m)) = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    push_cast
    rw [show -(1 / (2 * ((k : ℝ) + m))) * (2 * (k + m)) = -1 by field_simp, Real.rpow_neg_one,
      mul_inv_cancel₀ ht.ne']
  have hc2k : t * c ^ (2 * k) = t ^ ((m : ℝ) / (k + m)) := by
    have h1 := Real.rpow_add ht 1 (-(1 / (2 * ((k : ℝ) + m))) * (2 * k))
    rw [Real.rpow_one] at h1
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    push_cast
    rw [← h1]
    congr 1
    field_simp
    ring
  set s : ℝ := ε * t ^ ((m : ℝ) / (k + m)) with hs
  have hpt : ∀ u : ℝ, t * ((ε + (c * u) ^ (2 * m)) * (c * u) ^ (2 * k)) =
      s * u ^ (2 * k) + u ^ (2 * (k + m)) := by
    intro u
    have : t * ((ε + (c * u) ^ (2 * m)) * (c * u) ^ (2 * k)) =
        ε * (t * c ^ (2 * k)) * u ^ (2 * k) + (t * c ^ (2 * (k + m))) * u ^ (2 * (k + m)) := by
      ring
    rw [this, hc2k, hc2n, one_mul, hs]
  have hW : ∀ u : ℝ, |c * u| ^ h * Real.exp (-(t * ((ε + (c * u) ^ (2 * m)) * (c * u) ^ (2 * k)))) =
      c ^ h * wallW k m h s u := by
    intro u
    unfold wallW
    rw [hpt, abs_mul, abs_of_pos hcpos, mul_pow]
    ring
  have hn := Measure.integral_comp_mul_left (fun x : ℝ ↦ t * ((ε + x ^ (2 * m)) * x ^ (2 * k)) *
    (|x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k)))))) c
  have hd := Measure.integral_comp_mul_left
    (fun x : ℝ ↦ |x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k))))) c
  rw [abs_inv, abs_of_pos hcpos, smul_eq_mul] at hn hd
  simp only [hW] at hn hd
  simp only [hpt] at hn
  have hn' : (∫ x, t * ((ε + x ^ (2 * m)) * x ^ (2 * k)) *
      (|x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k)))))) =
      c * ∫ u, (s * u ^ (2 * k) + u ^ (2 * (k + m))) * (c ^ h * wallW k m h s u) := by
    rw [hn, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  have hd' : (∫ x, |x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k))))) =
      c * ∫ u, c ^ h * wallW k m h s u := by
    rw [hd, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  unfold wallEnergy wallCross
  rw [mul_div_assoc', ← integral_const_mul]
  have e0 : (fun x : ℝ ↦ t * ((ε + x ^ (2 * m)) * x ^ (2 * k) *
      (|x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k))))))) =
      fun x ↦ t * ((ε + x ^ (2 * m)) * x ^ (2 * k)) *
        (|x| ^ h * Real.exp (-(t * ((ε + x ^ (2 * m)) * x ^ (2 * k))))) := by
    funext x
    ring
  rw [e0, hn', hd']
  have e1 : (fun u : ℝ ↦ (s * u ^ (2 * k) + u ^ (2 * (k + m))) * (c ^ h * wallW k m h s u)) =
      fun u ↦ c ^ h * ((s * u ^ (2 * k) + u ^ (2 * (k + m))) * wallW k m h s u) := by
    funext u
    ring
  rw [e1, integral_const_mul, integral_const_mul, mul_div_mul_left _ _ hcpos.ne',
    mul_div_mul_left _ _ (pow_ne_zero _ hcpos.ne')]

end Laplace.Multi
