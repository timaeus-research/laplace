/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MomentBounds

/-!
# The abstract all-order one-dimensional kernel-jet transfer (grammar §4.2)

For `Z(N) = ∫₀^b u^h e^{-β(Nu^k)²} F(u, Nu^k) du` with an amplitude admitting a finite jet
expansion at `u = 0`,

  `|F(u, s) − ∑_{j<R} u^j F_j(s)| ≤ u^R H_R(s)`   (`0 ≤ u ≤ b`, `s > 0`),

with Gaussian-weighted moments finite, the density-transfer theorem gives, for `N ≥ 1`,

  `|Z(N) − ∑_{j<R} c_j N^{-q_j}| ≤ K_R N^{-q_R}`,  `q_j = (h+1+j)/k`,
  `c_j = k⁻¹ ∫₀^∞ s^{q_j-1} e^{-βs²} F_j(s) ds`

(`oneDKernel_jet_expansion`). This is the engine of the all-order theory: finite compatible jets
with moment-integrable remainders, no analyticity. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- The one-dimensional kernel integral with general amplitude `F(u, s)`, `s = N u^k`. -/
noncomputable def oneDKernel (β b N : ℝ) (h k : ℕ) (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) b, u ^ h * (Real.exp (-β * (N * u ^ k) ^ 2) * F u (N * u ^ k))

/-- The chart integral is the kernel integral with amplitude `η(u) e^{βsξ(u)}`. -/
theorem oneDScale_eq_oneDKernel (β b N : ℝ) (h k : ℕ) (ξ η : ℝ → ℝ) :
    oneDScale β b N h k ξ η = oneDKernel β b N h k (fun u s => η u * Real.exp (β * s * ξ u)) := by
  unfold oneDScale oneDKernel
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [show Real.exp (-β * (N * u ^ k) ^ 2 + β * (N * u ^ k) * ξ u)
    = Real.exp (-β * (N * u ^ k) ^ 2) * Real.exp (β * (N * u ^ k) * ξ u) by rw [← Real.exp_add]]
  ring

/-- The exact density `ρ(r, s) = k⁻¹ r^{p-1} F(r^{1/k}, s)`. -/
noncomputable def oneDKernelDensity (p : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (r s : ℝ) : ℝ :=
  1 / (k : ℝ) * r ^ (p - 1) * F (r ^ ((k : ℝ)⁻¹)) s

theorem oneDKernel_eq_transferZ (β b N : ℝ) (h k : ℕ) (hk : 0 < k) (hb : 0 < b)
    (F : ℝ → ℝ → ℝ) :
    oneDKernel β b N h k F = transferZ (oneDKernelDensity (((h : ℝ) + 1) / k) k F) β (b ^ k) N := by
  unfold oneDKernel transferZ oneDKernelDensity
  set g : ℝ → ℝ := fun x => Real.exp (-β * (N * x) ^ 2) * F (x ^ ((k : ℝ)⁻¹)) (N * x) with hg
  have hpt : ∀ u ∈ Ioc (0 : ℝ) b,
      u ^ h * (Real.exp (-β * (N * u ^ k) ^ 2) * F u (N * u ^ k)) = u ^ h * g (u ^ k) := by
    intro u hu
    simp only [hg]
    rw [Real.pow_rpow_inv_natCast hu.1.le hk.ne']
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_Ioc_pow_mul_comp_pow h k b g hk hb,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
  simp only [hg]
  ring

/-- The jet coefficient `c_j = k⁻¹ ∫₀^∞ s^{q_j - 1} e^{-βs²} F_j(s) ds`. -/
noncomputable def jetCoeff (β p : ℝ) (k : ℕ) (Fj : ℕ → ℝ → ℝ) (j : ℕ) : ℝ :=
  1 / (k : ℝ) * logMoment β (p + (j : ℝ) / k) 0 (Fj j)

/-- **The density expansion of the kernel density** from a finite jet of the amplitude. -/
theorem oneDKernelDensity_expansion (b p : ℝ) (k R : ℕ) (F : ℝ → ℝ → ℝ) (Fj : ℕ → ℝ → ℝ)
    (HR : ℝ → ℝ) (hb : 0 < b) (hk : 0 < k)
    (hFm : Measurable (Function.uncurry F)) (hFjm : ∀ j, Measurable (Fj j))
    (hHm : Measurable HR) (hH0 : ∀ s, 0 ≤ HR s)
    (hrem : ∀ u ∈ Icc (0 : ℝ) b, ∀ s, 0 < s →
      |F u s - ∑ j ∈ Finset.range R, u ^ j * Fj j s| ≤ u ^ R * HR s) :
    DensityExpansion (oneDKernelDensity p k F) (fun i : Fin R => p + (i : ℝ) / k) (fun _ => 0)
      (fun i : Fin R => fun s => 1 / (k : ℝ) * Fj i s) (p + (R : ℝ) / k) (b ^ k) 0
      (fun s => 1 / (k : ℝ) * HR s) where
  R_pos := by positivity
  α_lt := by
    intro i
    have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
    have : (i : ℝ) < R := by exact_mod_cast i.isLt
    have : (i : ℝ) / k < (R : ℝ) / k := div_lt_div_of_pos_right this hk'
    linarith
  j_le := fun _ => le_rfl
  ρ_meas := by
    unfold oneDKernelDensity Function.uncurry
    exact (measurable_const.mul (measurable_fst.pow_const _)).mul
      (hFm.comp ((measurable_fst.pow_const _).prodMk measurable_snd))
  c_meas := fun i => measurable_const.mul (hFjm i)
  H_meas := measurable_const.mul hHm
  H_nonneg := fun s => mul_nonneg (by positivity) (hH0 s)
  rem := by
    intro r hr s hs
    have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
    set u : ℝ := r ^ ((k : ℝ)⁻¹) with hu
    have hu0 : 0 < u := Real.rpow_pos_of_pos hr.1 _
    have hub : u ≤ b := by
      have : r ^ ((k : ℝ)⁻¹) ≤ (b ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow hr.1.le hr.2 (by positivity)
      rwa [Real.pow_rpow_inv_natCast hb.le hk.ne'] at this
    have hkey := hrem u ⟨hu0.le, hub⟩ s hs
    -- `r^{p + j/k - 1} = r^{p-1} u^j`
    have hpow : ∀ j : ℕ, r ^ (p + (j : ℝ) / k - 1) = r ^ (p - 1) * u ^ j := by
      intro j
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hr.1.le, ← Real.rpow_add hr.1]
      congr 1; field_simp; ring
    simp only [pow_zero, mul_one]
    rw [Fin.sum_univ_eq_sum_range (fun j => r ^ (p + (j : ℝ) / k - 1) * (1 / (k : ℝ) * Fj j s)) R]
    unfold oneDKernelDensity
    rw [← hu]
    have hexpr : 1 / (k : ℝ) * r ^ (p - 1) * F u s
        - ∑ j ∈ Finset.range R, r ^ (p + (j : ℝ) / k - 1) * (1 / (k : ℝ) * Fj j s)
        = 1 / (k : ℝ) * r ^ (p - 1) * (F u s - ∑ j ∈ Finset.range R, u ^ j * Fj j s) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hpow j]; ring
    rw [hexpr, abs_mul, abs_of_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hr.1.le _)),
      hpow R]
    calc 1 / (k : ℝ) * r ^ (p - 1) * |F u s - ∑ j ∈ Finset.range R, u ^ j * Fj j s|
        ≤ 1 / (k : ℝ) * r ^ (p - 1) * (u ^ R * HR s) :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg (by positivity) (Real.rpow_nonneg hr.1.le _))
      _ = _ := by ring

/-- **The all-order kernel-jet transfer**: for `N ≥ 1`,
`|Z(N) − ∑_{j<R} c_j N^{-q_j}| ≤ K_R N^{-q_R}`. -/
theorem oneDKernel_jet_expansion (β b p : ℝ) (h k R : ℕ) (F : ℝ → ℝ → ℝ) (Fj : ℕ → ℝ → ℝ)
    (HR : ℝ → ℝ) (hb : 0 < b) (hk : 0 < k) (hp : ((h : ℝ) + 1) / k = p)
    (hFm : Measurable (Function.uncurry F)) (hFjm : ∀ j, Measurable (Fj j))
    (hHm : Measurable HR) (hH0 : ∀ s, 0 ≤ HR s)
    (hrem : ∀ u ∈ Icc (0 : ℝ) b, ∀ s, 0 < s →
      |F u s - ∑ j ∈ Finset.range R, u ^ j * Fj j s| ≤ u ^ R * HR s)
    (hMc : ∀ j, j < R → IntegrableOn (fun s => s ^ (p + (j : ℝ) / k - 1) * (1 + |Real.log s|) ^ 0
      * (Real.exp (-β * s ^ 2) * |Fj j s|)) (Ioi 0))
    (hMt : ∀ j, j < R → IntegrableOn (fun s => s ^ (p + (R : ℝ) / k - 1) * (1 + |Real.log s|) ^ 0
      * (Real.exp (-β * s ^ 2) * |Fj j s|)) (Ioi 0))
    (hMH : IntegrableOn (fun s => s ^ (p + (R : ℝ) / k - 1) * (1 + |Real.log s|) ^ 0
      * (Real.exp (-β * s ^ 2) * HR s)) (Ioi 0)) :
    ∃ K : ℝ, ∀ N : ℝ, 1 ≤ N →
      |oneDKernel β b N h k F
          - ∑ j ∈ Finset.range R, jetCoeff β p k Fj j * N ^ (-(p + (j : ℝ) / k))|
        ≤ K * N ^ (-(p + (R : ℝ) / k)) := by
  have hD := oneDKernelDensity_expansion b p k R F Fj HR hb hk hFm hFjm hHm hH0 hrem
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hkinv : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  -- the moment hypotheses for the scaled coefficients
  have hMc' : ∀ i : Fin R, IntegrableOn (fun s => s ^ ((fun i : Fin R => p + (i : ℝ) / k) i - 1)
      * (1 + |Real.log s|) ^ ((fun _ : Fin R => (0 : ℕ)) i)
      * (Real.exp (-β * s ^ 2) * |(fun i : Fin R => fun s => 1 / (k : ℝ) * Fj i s) i s|))
      (Ioi 0) := by
    intro i
    have this : IntegrableOn (fun s => 1 / (k : ℝ) * (s ^ (p + (i : ℝ) / k - 1)
        * (1 + |Real.log s|) ^ 0 * (Real.exp (-β * s ^ 2) * |Fj i s|))) (Ioi 0) :=
      (hMc i i.isLt).const_mul (1 / (k : ℝ))
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [abs_mul, abs_of_nonneg hkinv]
    ring
  have hMt' : ∀ i : Fin R, IntegrableOn (fun s => s ^ (p + (R : ℝ) / k - 1)
      * (1 + |Real.log s|) ^ ((fun _ : Fin R => (0 : ℕ)) i)
      * (Real.exp (-β * s ^ 2) * |(fun i : Fin R => fun s => 1 / (k : ℝ) * Fj i s) i s|))
      (Ioi 0) := by
    intro i
    have this : IntegrableOn (fun s => 1 / (k : ℝ) * (s ^ (p + (R : ℝ) / k - 1)
        * (1 + |Real.log s|) ^ 0 * (Real.exp (-β * s ^ 2) * |Fj i s|))) (Ioi 0) :=
      (hMt i i.isLt).const_mul (1 / (k : ℝ))
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [abs_mul, abs_of_nonneg hkinv]
    ring
  have hMH' : IntegrableOn (fun s => s ^ (p + (R : ℝ) / k - 1) * (1 + |Real.log s|) ^ 0
      * (Real.exp (-β * s ^ 2) * (1 / (k : ℝ) * HR s))) (Ioi 0) := by
    have this : IntegrableOn (fun s => 1 / (k : ℝ) * (s ^ (p + (R : ℝ) / k - 1)
        * (1 + |Real.log s|) ^ 0 * (Real.exp (-β * s ^ 2) * HR s))) (Ioi 0) :=
      hMH.const_mul (1 / (k : ℝ))
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    beta_reduce; ring
  refine ⟨envMoment β (p + (R : ℝ) / k) 0 (fun s => 1 / (k : ℝ) * HR s)
    + ∑ i : Fin R, (b ^ k) ^ (p + (i : ℝ) / k - (p + (R : ℝ) / k))
      * tailMoment β (p + (R : ℝ) / k) 0 (fun s => 1 / (k : ℝ) * Fj i s), fun N hN => ?_⟩
  have hmain := densityTransfer_bound hD β hMc' hMt' hMH' N hN
  have hZ := oneDKernel_eq_transferZ β b N h k hk hb F
  rw [hp] at hZ
  rw [pow_zero, mul_one, ← hZ] at hmain
  have hterm : ∀ i : Fin R, transferTerm β (p + (i : ℝ) / k) 0 (fun s => 1 / (k : ℝ) * Fj i s) N
      = jetCoeff β p k Fj i * N ^ (-(p + (i : ℝ) / k)) := by
    intro i
    rw [transferTerm_zero, jetCoeff, logMoment_const_mul]
    ring
  simp only [hterm] at hmain
  rw [Fin.sum_univ_eq_sum_range (fun j => jetCoeff β p k Fj j * N ^ (-(p + (j : ℝ) / k))) R]
    at hmain
  calc _ ≤ _ := hmain
    _ = _ := mul_comm _ _

end Laplace.Grammar
