/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.BoundedXi

/-!
# The one-dimensional standard integral at a general scale (grammar §4.2, state-density machinery)

The state-density programme integrates the one-dimensional theory along the exceptional divisor.
For that the one-dimensional standard integral is needed as a function of an arbitrary scale
`c → ∞` (rather than `√n`), with continuous data `ξ, η` Lipschitz at `0`:

* `oneDScale β b c h k ξ η = ∫₀^b u^h η(u) e^{-β(cu^k)² + β cu^k ξ(u)} du`;
* **leading term** (from unit 34 via `n = c²`): `c^p · oneDScale → (1/k) A_{p-1}(ξ(0)) η(0)`,
  `p = (h+1)/k`, `A_{p-1}(a) = ∫₀^∞ s^{p-1} e^{-βs² + βas} ds` (`oneDScale_tendsto`);
* **uniform bound**: `c^p |oneDScale| ≤ M e^{βL²/2} (1/k) ∫₀^∞ s^{p-1} e^{-(β/2)s²} ds` for all
  `c > 0`, where `|ξ| ≤ L`, `|η| ≤ M` on `(0,b]` (`oneDScale_abs_le`).

Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Laplace.Grammar

/-- The one-dimensional standard integral at scale `c` with data `ξ, η`. -/
noncomputable def oneDScale (β b c : ℝ) (h k : ℕ) (ξ η : ℝ → ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) b, u ^ h * η u * Real.exp (-β * (c * u ^ k) ^ 2 + β * (c * u ^ k) * ξ u)

/-- At scale `c > 0` this is unit 34's integral at `n = c²`. -/
theorem oneDScale_eq_sq (β b c : ℝ) (h k : ℕ) (ξ η : ℝ → ℝ) (hc : 0 < c) :
    oneDScale β b c h k ξ η = ∫ u in Ioc (0 : ℝ) b,
      u ^ h * η u
        * Real.exp (-β * (c ^ 2) * u ^ (2 * k) + β * Real.sqrt (c ^ 2) * u ^ k * ξ u) := by
  unfold oneDScale
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [Real.sqrt_sq hc.le, mul_pow, ← pow_mul, mul_comm k 2]
  ring_nf

/-- **Leading term at a general scale**: `c^p · oneDScale(c) → (1/k) A_{p-1}(ξ₀) η₀` as `c → ∞`. -/
theorem oneDScale_tendsto (β ξ₀ η₀ b C C' : ℝ) (ξ η : ℝ → ℝ) (h k : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hk : 0 < k) (hC : 0 ≤ C) (hξc : Continuous ξ) (hηc : Continuous η)
    (hξ : ∀ u ∈ Ioc (0 : ℝ) b, |ξ u - ξ₀| ≤ C * u) (hη : ∀ u ∈ Ioc (0 : ℝ) b, |η u - η₀| ≤ C' * u) :
    Tendsto (fun c : ℝ => c ^ (((h : ℝ) + 1) / k) * oneDScale β b c h k ξ η) atTop
      (𝓝 (1 / (k : ℝ) * weightedMass β ξ₀ (((h : ℝ) + 1) / k - 1) * η₀)) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  set p : ℝ := ((h : ℝ) + 1) / k with hp
  have hp0 : 0 < p := by positivity
  -- unit 34 in the form n^{p/2} F(n) − η₀ K → 0
  have hbig := standardIntegral1D_leading_isBigO_of_lipschitz β ξ₀ η₀ b C C' ξ η h k hβ hb hk hC hξc
    hηc hξ hη
  set K : ℝ := η₀ * ((1 / (2 * (k : ℝ))) * fluctuation β (((h : ℝ) + 1) / (2 * k)) ξ₀) with hK
  set F : ℝ → ℝ := fun n => ∫ u in Ioc (0 : ℝ) b,
    u ^ h * η u * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ u) with hF
  have hlim : Tendsto (fun n : ℝ => n ^ (p / 2) * F n) atTop (𝓝 K) := by
    -- n^{p/2}(F n − K n^{-p/2}) = O(n^{-1/(2k)}) → 0
    have h1 : (fun n : ℝ => n ^ (p / 2) * (F n - K * n ^ (-(((h : ℝ) + 1) / (2 * k)))))
        =O[atTop] fun n : ℝ => n ^ (-(1 / (2 * (k : ℝ)))) := by
      have := (isBigO_refl (fun n : ℝ => n ^ (p / 2)) atTop).mul hbig
      refine this.trans (IsBigO.of_bound 1 ?_)
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos hn _), abs_of_pos (Real.rpow_pos_of_pos hn _),
        abs_of_pos (Real.rpow_pos_of_pos hn _), ← Real.rpow_add hn]
      apply le_of_eq
      congr 1
      rw [hp]; field_simp; ring
    have h2 : Tendsto (fun n : ℝ => n ^ (-(1 / (2 * (k : ℝ))))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by positivity)
    have h3 : Tendsto (fun n : ℝ => n ^ (p / 2) * (F n - K * n ^ (-(((h : ℝ) + 1) / (2 * k)))))
        atTop (𝓝 0) := h1.trans_tendsto h2
    have h4 : Tendsto (fun n : ℝ => n ^ (p / 2) * (F n - K * n ^ (-(((h : ℝ) + 1) / (2 * k)))) + K)
        atTop (𝓝 (0 + K)) := h3.add_const K
    rw [zero_add] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    have : n ^ (p / 2) * n ^ (-(((h : ℝ) + 1) / (2 * k))) = 1 := by
      rw [← Real.rpow_add hn, hp, show ((h : ℝ) + 1) / k / 2 + -(((h : ℝ) + 1) / (2 * k)) = 0 by
        field_simp; ring, Real.rpow_zero]
    calc n ^ (p / 2) * (F n - K * n ^ (-(((h : ℝ) + 1) / (2 * k)))) + K
        = n ^ (p / 2) * F n - K * (n ^ (p / 2) * n ^ (-(((h : ℝ) + 1) / (2 * k)))) + K := by ring
      _ = n ^ (p / 2) * F n := by rw [this]; ring
  -- compose with n = c²
  have hsq : Tendsto (fun c : ℝ => c ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hcomp := hlim.comp hsq
  have hKval : K = 1 / (k : ℝ) * weightedMass β ξ₀ (p - 1) * η₀ := by
    rw [hK, weightedMass_eq, show (p - 1 + 1) / 2 = ((h : ℝ) + 1) / (2 * k) by
      rw [hp]; field_simp; ring]
    ring
  rw [hKval] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  simp only [Function.comp]
  rw [oneDScale_eq_sq β b c h k ξ η hc]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  congr 1
  push_cast; ring

/-- **Uniform bound**: for `c > 0`, `|ξ| ≤ L` and `|η| ≤ M` on `(0,b]`,
`c^p |oneDScale(c)| ≤ M e^{βL²/2} (1/k) ∫₀^∞ s^{p-1} e^{-(β/2)s²} ds`. -/
theorem oneDScale_abs_le (β b c L M : ℝ) (h k : ℕ) (ξ η : ℝ → ℝ) (hβ : 0 < β) (hb : 0 < b)
    (hk : 0 < k) (hc : 0 < c) (hM : 0 ≤ M)
    (hξL : ∀ u ∈ Ioc (0 : ℝ) b, |ξ u| ≤ L) (hηM : ∀ u ∈ Ioc (0 : ℝ) b, |η u| ≤ M) :
    c ^ (((h : ℝ) + 1) / k) * |oneDScale β b c h k ξ η|
      ≤ M * Real.exp (β * L ^ 2 / 2) * (1 / (k : ℝ))
        * weightedMass (β / 2) 0 (((h : ℝ) + 1) / k - 1) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  set p : ℝ := ((h : ℝ) + 1) / k with hp
  have hp0 : 0 < p := by positivity
  have hcp : 0 < c ^ p := Real.rpow_pos_of_pos hc p
  set E : ℝ := Real.exp (β * L ^ 2 / 2) with hE
  -- pointwise domination on (0, b]
  have hpt : ∀ u ∈ Ioc (0 : ℝ) b,
      ‖u ^ h * η u * Real.exp (-β * (c * u ^ k) ^ 2 + β * (c * u ^ k) * ξ u)‖
        ≤ M * E * (u ^ h * Real.exp (-(β / 2) * (c * u ^ k) ^ 2)) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hs0 : 0 ≤ c * u ^ k := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hu0.le _),
      abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-β * (c * u ^ k) ^ 2 + β * (c * u ^ k) * ξ u)
        ≤ Real.exp (-β * (c * u ^ k) ^ 2 + β * (c * u ^ k) * L) := by
      apply Real.exp_le_exp.2
      have := (abs_le.1 (hξL u hu)).2
      nlinarith [mul_nonneg hβ.le hs0]
    have h2 : Real.exp (-β * (c * u ^ k) ^ 2 + β * (c * u ^ k) * L)
        ≤ Real.exp (-(β / 2) * (c * u ^ k) ^ 2 + β * L ^ 2 / 2) := by
      calc Real.exp (-β * (c * u ^ k) ^ 2 + β * (c * u ^ k) * L)
          = Real.exp (-β * (c * u ^ k) ^ 2 + β * L * Real.sqrt ((c * u ^ k) ^ 2)) := by
            rw [Real.sqrt_sq hs0]; ring_nf
        _ ≤ _ := fluctuation_integrand_le β L _ hβ (sq_nonneg _)
    calc u ^ h * |η u| * Real.exp (-β * (c * u ^ k) ^ 2 + β * (c * u ^ k) * ξ u)
        ≤ u ^ h * M * Real.exp (-(β / 2) * (c * u ^ k) ^ 2 + β * L ^ 2 / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hηM u hu) (pow_nonneg hu0.le _)) (h1.trans h2)
            (Real.exp_pos _).le (by positivity)
      _ = M * E * (u ^ h * Real.exp (-(β / 2) * (c * u ^ k) ^ 2)) := by
          rw [hE, Real.exp_add]; ring
  -- the Gaussian integral at scale c
  have hgauss : (∫ u in Ioc (0 : ℝ) b, u ^ h * Real.exp (-(β / 2) * (c * u ^ k) ^ 2))
      ≤ 1 / (k : ℝ) * c ^ (-p) * weightedMass (β / 2) 0 (p - 1) := by
    have hsub := integral_Ioc_pow_mul_comp_pow h k b
      (fun s => Real.exp (-(β / 2) * (c * s) ^ 2)) hk hb
    rw [hsub, ← hp,
      integral_Ioc_rpow_mul_comp_mul_left (p - 1) c (b ^ k) (fun x => Real.exp (-(β / 2) * x ^ 2))
        hc (by positivity), show p - 1 + 1 = p by ring]
    have hint := weightedKernel_integrableOn (β / 2) 0 (p - 1) (by positivity) (by linarith)
    have hK : ∀ x : ℝ, x ^ (p - 1) * Real.exp (-(β / 2) * x ^ 2)
        = x ^ (p - 1) * quadKernel (β / 2) 0 x := by
      intro x; simp [quadKernel]
    simp_rw [hK]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hc.le _)
    exact setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun x hx =>
        mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (quadKernel_pos _ _ _).le))
      (Filter.Eventually.of_forall fun x hx => Ioc_subset_Ioi_self hx)
  -- assemble
  have hint2 : IntegrableOn (fun u : ℝ => u ^ h * Real.exp (-(β / 2) * (c * u ^ k) ^ 2))
      (Ioc 0 b) :=
    (by fun_prop : Continuous fun u : ℝ => u ^ h * Real.exp (-(β / 2) * (c * u ^ k) ^ 2))
      |>.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have habs : |oneDScale β b c h k ξ η|
      ≤ M * E * ∫ u in Ioc (0 : ℝ) b, u ^ h * Real.exp (-(β / 2) * (c * u ^ k) ^ 2) := by
    rw [oneDScale, ← Real.norm_eq_abs, ← MeasureTheory.integral_const_mul]
    refine norm_integral_le_of_norm_le (hint2.const_mul _) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall hpt
  have hME : 0 ≤ M * E := mul_nonneg hM (Real.exp_pos _).le
  calc c ^ p * |oneDScale β b c h k ξ η|
      ≤ c ^ p * (M * E * (1 / (k : ℝ) * c ^ (-p) * weightedMass (β / 2) 0 (p - 1))) :=
        mul_le_mul_of_nonneg_left (habs.trans (mul_le_mul_of_nonneg_left hgauss hME)) hcp.le
    _ = M * E * (1 / (k : ℝ)) * weightedMass (β / 2) 0 (p - 1) * (c ^ p * c ^ (-p)) := by ring
    _ = M * E * (1 / (k : ℝ)) * weightedMass (β / 2) 0 (p - 1) := by
        rw [← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero, mul_one]

end Laplace.Grammar
