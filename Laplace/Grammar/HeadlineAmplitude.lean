/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonomialAmplitudeAsymptotic

/-!
# Headline statements, part VIII: the dressed normal moment integral

Paper-facing wrappers for units 184–186 (the continuous-amplitude milestone). For the dressed normal
moment integral `I_η(N) = ∫_{(0,1]^{m+1}} η(x) x^h e^{-βN x^{2k}} dx` with a continuous amplitude
`η`, Mellin ratios `ℓᵢ = (hᵢ+1)/(2kᵢ)`, minimum `λ` attained on `J`:

* the **face-supported leading functional** (`headline_normal_moment_amplitude`):
  `I_η(N)/(N^{-λ}(log N)^{|J|-1}) → Γ(λ)β^{-λ}/(|J|-1)! ∏_{j∈J} 1/(2kⱼ) ·
     ∫_{(0,1]^{m+1}} η(P_J u) ∏_{i∉J} uᵢ^{hᵢ-2kᵢλ} du`, with `P_J` zeroing the minimal coordinates;
* **constant amplitude** recovers the bare mixed constant (`amplitudeCoeff_const`);
* **equal ratios**: the coefficient is `η(0)` times the bare constant
  (`headline_normal_moment_amplitude_equal`). Under the standing hypotheses, origin evaluation
  holds for *every* continuous amplitude exactly when all ratios are equal; particular amplitudes
  (e.g. constants) satisfy it also for unequal ratios, while `η(u) = uᵢ` with `i ∉ J` vanishes at
  the origin yet has a strictly positive face coefficient;
* **face-vanishing amplitude**: the coefficient is `0` (`amplitudeCoeff_eq_zero_of_face`), so the
  dressed integral is `o` of the bare scale (no quantitative next-order claim);
* the **equivalence form** under `amplitudeCoeff ≠ 0` (`headline_normal_moment_amplitude_equiv`).

Scope: nonempty block of boundary-type coordinates, unit cutoff, `kᵢ > 0`, fixed `β > 0`, amplitude
continuous on `ℝ^{m+1}`. NOT claimed: interior coordinates with parity factors, tangential
amplitudes, stochastic phases, or the full expectation expansion. Zero `sorry`/`axiom`.
-/

open Asymptotics Filter MeasureTheory Set Topology

namespace Laplace.Grammar

theorem volume_unitBox (d : ℕ) : (volume : Measure (Fin d → ℝ)) (unitBox d) = 1 := by
  unfold unitBox
  rw [volume_pi_pi]
  simp [Real.volume_Ioc]

/-- **Constant amplitude**: the face functional of a constant is the bare mixed constant. -/
theorem amplitudeCoeff_const {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) (c : ℝ) :
    amplitudeCoeff h k l β (fun _ => c) = c * monomialMixedConst h k l β := by
  have h0 := face_moment_eq h k hk l β hmin (fun _ => 0) (fun _ _ => rfl)
  simp only [pow_zero, Finset.prod_const_one, one_mul, add_zero] at h0
  unfold amplitudeCoeff
  rw [← h0, ← integral_const_mul, ← integral_const_mul]
  exact setIntegral_congr_fun (measurableSet_unitBox d) fun u _ => by ring

/-- **Face-vanishing amplitude**: if `η` vanishes on the face `u_J = 0` (over the box), the
leading coefficient vanishes, so the dressed integral is `o(N^{-λ} (log N)^{|J|-1})`; no
quantitative improvement of the exponent or log power is claimed. -/
theorem amplitudeCoeff_eq_zero_of_face {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ)
    (η : (Fin d → ℝ) → ℝ) (hη : ∀ u ∈ unitBox d, η (faceProj h k l u) = 0) :
    amplitudeCoeff h k l β η = 0 := by
  unfold amplitudeCoeff
  rw [setIntegral_congr_fun (measurableSet_unitBox d) (fun u hu => by rw [hη u hu, zero_mul]),
    integral_zero, mul_zero]

/-- **Equal ratios**: the face is the origin and the coefficient is `η(0)` times the bare constant
`Γ(λ) β^{-λ} / (d! ∏ᵢ 2kᵢ)`. -/
theorem amplitudeCoeff_equal (d : ℕ) (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    (hratio : ∀ i, ratioExp h k i = l) (η : (Fin (d + 1) → ℝ) → ℝ) :
    amplitudeCoeff h k l β η =
      η 0 * (Real.Gamma l * β ^ (-l) / ((d.factorial : ℝ) * ∏ i, 2 * (k i : ℝ))) := by
  unfold amplitudeCoeff faceLeadConst
  have hP : ∀ u, faceProj h k l u = 0 := fun u => funext fun i => by simp [faceProj, hratio i]
  have hR : ∀ u, residualWeight h k l u = 1 := fun u =>
    Finset.prod_eq_one fun i _ => by simp [hratio i]
  simp only [hP, hR, mul_one]
  rw [setIntegral_const, measureReal_def, volume_unitBox, ENNReal.toReal_one, one_smul]
  have hm : multCount (ratioExp h k) l = d + 1 := by
    unfold multCount
    simp [hratio]
  rw [hm, Nat.add_sub_cancel]
  have hprod : (∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else (1 : ℝ)) =
      (∏ i, 2 * (k i : ℝ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [if_pos (hratio i), one_div]
  rw [hprod]
  ring

/-- **Dressed normal moment asymptotic** (face-supported leading functional). -/
theorem headline_normal_moment_amplitude (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hmin : ∀ i, l ≤ ((h i : ℝ) + 1) / (2 * (k i : ℝ)))
    (hatt : ∃ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l)
    (η : (Fin (m + 1) → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => (∫ x in unitBox (m + 1),
        η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) *
          Real.log N ^ ((∑ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 else 0) - 1)))
      atTop
      (𝓝 ((Real.Gamma l * β ^ (-l) /
          (((∑ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 else 0) - 1).factorial : ℝ) *
          ∏ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 / (2 * (k i : ℝ)) else 1) *
        ∫ u in unitBox (m + 1),
          η (fun i => if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 0 else u i) *
            ∏ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then (1 : ℝ)
              else u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * l))) :=
  amplitude_tendsto m h k hk l β hl hβ hmin hatt η hη

/-- **Equal ratios, continuous amplitude**:
`I_η(N)/(N^{-λ}(log N)^m) → η(0) Γ(λ)β^{-λ}/(m! ∏ 2kᵢ)`. -/
theorem headline_normal_moment_amplitude_equal (m : ℕ) (h k : Fin (m + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l)
    (η : (Fin (m + 1) → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => (∫ x in unitBox (m + 1),
        η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) * Real.log N ^ m)) atTop
      (𝓝 (η 0 * (Real.Gamma l * β ^ (-l) / ((m.factorial : ℝ) * ∏ i, 2 * (k i : ℝ))))) := by
  have hm : multCount (ratioExp h k) l = m + 1 := by
    unfold multCount
    simp [ratioExp, hratio]
  have hT := amplitude_tendsto m h k hk l β hl hβ (fun i => (hratio i).symm.le) ⟨0, hratio 0⟩ η hη
  rw [amplitudeCoeff_equal m h k l β hratio η, hm, Nat.add_sub_cancel] at hT
  exact hT

/-- **Equivalence form** when the face coefficient is nonzero. -/
theorem headline_normal_moment_amplitude_equiv (m : ℕ) (h k : Fin (m + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (η : (Fin (m + 1) → ℝ) → ℝ) (hη : Continuous η)
    (hc : amplitudeCoeff h k l β η ≠ 0) :
    (fun N => ∫ x in unitBox (m + 1),
        η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) ~[atTop]
      fun N => amplitudeCoeff h k l β η * N ^ (-l) *
        Real.log N ^ (multCount (ratioExp h k) l - 1) := by
  refine isEquivalent_of_tendsto_one ?_
  have hT := (amplitude_tendsto m h k hk l β hl hβ hmin hatt η hη).div_const
    (amplitudeCoeff h k l β η)
  rw [div_self hc] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  simp only [Pi.div_apply]
  field_simp

end Laplace.Grammar
