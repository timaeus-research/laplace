/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TaylorTreeNormalisation

/-!
# Finite parts of power series (grammar §4.2, Astra #8 rank 4)

For a power series `a(v) = ∑_j z_j v^j` with a weighted-geometric coefficient bound
`|z_j| ρ^j ≤ H`, `0 < b < ρ`, the weighted finite part at any admissible truncation order `J > γ`
is the termwise absolutely convergent series

  `FP_γ(a) = ∑_j z_j · axisPrim γ b j`,   `axisPrim γ b j = b^{j−γ}/(j−γ)` (`log b` at `j = γ`)

(`axisFinitePart_series`). Proof: the Taylor remainder is the tail `∑_{j ≥ J} z_j v^j`, the
weighted tail `∑_{j≥J} z_j v^{j−1−γ}` has termwise integrals `z_j b^{j−γ}/(j−γ)` dominated by a
geometric series, so the Bochner integral and the sum commute
(`hasSum_integral_of_summable_integral_norm`); no `ε → 0` limit is needed. Applied to the analytic
faces, the canonical coefficient functions of `CanonicalCoefficients` become explicit series:
`U_{α_i}(s) = k₁⁻¹ ∑_j c_{ij}(s) axisPrim γ_i b j` (`canonU_anaFaceU_series`), and symmetrically
for `V`. This is the paper's "coefficients are absolutely convergent series" claim for the face
data. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- Summability of a power series with a weighted-geometric coefficient bound. -/
theorem summable_pow_of_majorant (z : ℕ → ℝ) (ρ H v : ℝ) (hρ : 0 < ρ)
    (hz : ∀ j, |z j| * ρ ^ j ≤ H) (hv : 0 ≤ v) (hvρ : v < ρ) :
    Summable fun j : ℕ => z j * v ^ j := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    ((summable_geometric_of_lt_one (by positivity) ((div_lt_one hρ).2 hvρ)).mul_left H)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hv]
  exact coeff_geometric_bound (z j) H v ρ j hv hρ (hz j)

/-- The finite part depends only on the function's values on `(0, b]`. -/
theorem axisFinitePart_congr (γ b : ℝ) (f g : ℝ → ℝ) (fm : ℕ → ℝ) (M : ℕ)
    (h : ∀ v ∈ Ioc (0 : ℝ) b, f v = g v) :
    axisFinitePart γ b f fm M = axisFinitePart γ b g fm M := by
  unfold axisFinitePart regAxisIntegral
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
  unfold taylorRem
  rw [h v hv]

/-- **The finite part of a power series is the termwise series**, absolutely convergent. -/
theorem axisFinitePart_series (γ b ρ H : ℝ) (hb : 0 < b) (hbρ : b < ρ) (z : ℕ → ℝ)
    (hz : ∀ j, |z j| * ρ ^ j ≤ H) (J : ℕ) (hJ : γ < J) :
    (Summable fun j : ℕ => z j * axisPrim γ b j) ∧
      axisFinitePart γ b (fun v => ∑' j : ℕ, z j * v ^ j) z J
        = ∑' j : ℕ, z j * axisPrim γ b j := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  have hr0 : 0 ≤ b / ρ := by positivity
  have hr1 : b / ρ < 1 := (div_lt_one hρ).2 hbρ
  have hH : 0 ≤ H := le_trans (by positivity) (hz 0)
  have hJγ : 0 < (J : ℝ) - γ := by linarith
  -- the exponents of the shifted, weighted terms
  set e : ℕ → ℝ := fun j => ((j + J : ℕ) : ℝ) - 1 - γ with he
  have hjJ : ∀ j : ℕ, (J : ℝ) ≤ ((j + J : ℕ) : ℝ) := fun j => by
    push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have he1 : ∀ j, -1 < e j := fun j => by
    simp only [he]; linarith [hjJ j]
  have he2 : ∀ j, e j + 1 = ((j + J : ℕ) : ℝ) - γ := fun j => by simp only [he]; ring
  have hne : ∀ j : ℕ, ((j + J : ℕ) : ℝ) ≠ γ := fun j h => by linarith [hjJ j]
  -- the weighted remainder is the shifted series
  have hrem : ∀ v ∈ Ioc (0 : ℝ) b,
      v ^ (-1 - γ) * taylorRem (fun v => ∑' j : ℕ, z j * v ^ j) z J v
        = ∑' j : ℕ, z (j + J) * v ^ e j := by
    intro v hv
    have hs := summable_pow_of_majorant z ρ H v hρ hz hv.1.le (lt_of_le_of_lt hv.2 hbρ)
    simp only [taylorRem]
    rw [← hs.sum_add_tsum_nat_add J, add_sub_cancel_left, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [show e j = ((j + J : ℕ) : ℝ) + (-1 - γ) by simp only [he]; ring, Real.rpow_add hv.1,
      Real.rpow_natCast]
    ring
  -- termwise integrability, values, and summable `L¹` norms
  have hint : ∀ j : ℕ,
      Integrable (fun v => z (j + J) * v ^ e j) (volume.restrict (Ioc (0 : ℝ) b)) := fun j =>
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b) (he1 j)).1).const_mul _
  have hval : ∀ j : ℕ,
      ∫ v in Ioc (0 : ℝ) b, z (j + J) * v ^ e j = z (j + J) * axisPrim γ b (j + J) := by
    intro j
    rw [integral_const_mul, integral_rpow_Ioc_zero b _ hb (he1 j), he2 j]
    unfold axisPrim
    rw [if_neg (hne j)]
  have hnorm : ∀ j : ℕ, ∫ v in Ioc (0 : ℝ) b, ‖z (j + J) * v ^ e j‖
      ≤ (H * b ^ (-γ) / ((J : ℝ) - γ) * (b / ρ) ^ J) * (b / ρ) ^ j := by
    intro j
    have hpt : ∀ v ∈ Ioc (0 : ℝ) b, ‖z (j + J) * v ^ e j‖ = |z (j + J)| * v ^ e j := by
      intro v hv
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv.1.le _)]
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_const_mul,
      integral_rpow_Ioc_zero b _ hb (he1 j), he2 j]
    have hpos : 0 < ((j + J : ℕ) : ℝ) - γ := by linarith [hjJ j]
    have hb1 : b ^ (((j + J : ℕ) : ℝ) - γ) = b ^ (j + J) * b ^ (-γ) := by
      rw [Real.rpow_sub hb, Real.rpow_natCast, Real.rpow_neg hb.le, div_eq_mul_inv]
    have hz1 : |z (j + J)| * b ^ (j + J) ≤ H * (b / ρ) ^ (j + J) :=
      coeff_geometric_bound _ H b ρ _ hb.le hρ (hz _)
    have hinv : 1 / (((j + J : ℕ) : ℝ) - γ) ≤ 1 / ((J : ℝ) - γ) :=
      one_div_le_one_div_of_le hJγ (by linarith [hjJ j])
    calc |z (j + J)| * (b ^ (((j + J : ℕ) : ℝ) - γ) / (((j + J : ℕ) : ℝ) - γ))
        = (|z (j + J)| * b ^ (j + J)) * b ^ (-γ) * (1 / (((j + J : ℕ) : ℝ) - γ)) := by
          rw [hb1]; ring
      _ ≤ (H * (b / ρ) ^ (j + J)) * b ^ (-γ) * (1 / ((J : ℝ) - γ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hz1 (by positivity)) hinv
            (one_div_pos.2 hpos).le (mul_nonneg (mul_nonneg hH (by positivity)) (by positivity))
      _ = (H * b ^ (-γ) / ((J : ℝ) - γ) * (b / ρ) ^ J) * (b / ρ) ^ j := by
          rw [pow_add]; ring
  have hsum : Summable fun j : ℕ => ∫ v in Ioc (0 : ℝ) b, ‖z (j + J) * v ^ e j‖ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun v => norm_nonneg _) hnorm
      ((summable_geometric_of_lt_one hr0 hr1).mul_left _)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  -- identify the regularised integral with the tail series
  have hreg : regAxisIntegral γ b (fun v => ∑' j : ℕ, z j * v ^ j) z J
      = ∑' j : ℕ, z (j + J) * axisPrim γ b (j + J) := by
    unfold regAxisIntegral
    rw [setIntegral_congr_fun measurableSet_Ioc hrem, ← h.tsum_eq]
    exact tsum_congr fun j => hval j
  have htail : Summable fun j : ℕ => z (j + J) * axisPrim γ b (j + J) :=
    h.summable.congr fun j => hval j
  have hall : Summable fun j : ℕ => z j * axisPrim γ b j := (summable_nat_add_iff J).1 htail
  refine ⟨hall, ?_⟩
  unfold axisFinitePart
  rw [hreg, add_comm, hall.sum_add_tsum_nat_add J]

/-- The row bound `|c_{ij}(s)| ρ^j ≤ H(s)/ρ^i` from the double-series envelope. -/
theorem row_majorant (c : ℕ × ℕ → ℝ → ℝ) (ρ : ℝ) (H : ℝ → ℝ) (hρ : 0 < ρ)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (i : ℕ) (s : ℝ) (j : ℕ) :
    |c (i, j) s| * ρ ^ j ≤ H s / ρ ^ i := by
  rw [le_div_iff₀ (pow_pos hρ i)]
  calc |c (i, j) s| * ρ ^ j * ρ ^ i = |c (i, j) s| * ρ ^ (i + j) := by rw [pow_add]; ring
    _ ≤ H s := hc (i, j) s

theorem col_majorant (c : ℕ × ℕ → ℝ → ℝ) (ρ : ℝ) (H : ℝ → ℝ) (hρ : 0 < ρ)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (j : ℕ) (s : ℝ) (i : ℕ) :
    |c (i, j) s| * ρ ^ i ≤ H s / ρ ^ j := by
  rw [le_div_iff₀ (pow_pos hρ j)]
  calc |c (i, j) s| * ρ ^ i * ρ ^ j = |c (i, j) s| * ρ ^ (i + j) := by rw [pow_add]; ring
    _ ≤ H s := hc (i, j) s

/-- The `u`-face finite-part coefficient as an explicit series. -/
theorem faceFPCoeff_anaFaceU_series (c : ℕ × ℕ → ℝ → ℝ) (b ρ γ : ℝ) (H : ℝ → ℝ) (hb : 0 < b)
    (hbρ : b < ρ) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (k i J : ℕ) (hJ : γ < J)
    (s : ℝ) :
    faceFPCoeff γ b k (anaFaceU c b i) (fun m => c (i, m)) J s
      = 1 / (k : ℝ) * ∑' j : ℕ, c (i, j) s * axisPrim γ b j := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  unfold faceFPCoeff
  congr 1
  have hcongr : axisFinitePart γ b (fun v => anaFaceU c b i v s) (fun m => c (i, m) s) J
      = axisFinitePart γ b (fun v => ∑' j : ℕ, c (i, j) s * v ^ j) (fun m => c (i, m) s) J := by
    refine axisFinitePart_congr γ b _ _ _ J fun v hv => ?_
    unfold anaFaceU faceU
    rw [clampB_of_mem b v (Ioc_subset_Icc_self hv)]
  rw [hcongr, (axisFinitePart_series γ b ρ _ hb hbρ (fun j => c (i, j) s)
    (row_majorant c ρ H hρ hc i s) J hJ).2]

/-- The `v`-face finite-part coefficient as an explicit series. -/
theorem faceFPCoeff_anaFaceV_series (c : ℕ × ℕ → ℝ → ℝ) (b ρ γ : ℝ) (H : ℝ → ℝ) (hb : 0 < b)
    (hbρ : b < ρ) (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (k j J : ℕ) (hJ : γ < J)
    (s : ℝ) :
    faceFPCoeff γ b k (anaFaceV c b j) (fun m => c (m, j)) J s
      = 1 / (k : ℝ) * ∑' i : ℕ, c (i, j) s * axisPrim γ b i := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  unfold faceFPCoeff
  congr 1
  have hcongr : axisFinitePart γ b (fun u => anaFaceV c b j u s) (fun m => c (m, j) s) J
      = axisFinitePart γ b (fun u => ∑' i : ℕ, c (i, j) s * u ^ i) (fun m => c (m, j) s) J := by
    refine axisFinitePart_congr γ b _ _ _ J fun u hu => ?_
    unfold anaFaceV faceV
    rw [clampB_of_mem b u (Ioc_subset_Icc_self hu)]
  rw [hcongr, (axisFinitePart_series γ b ρ _ hb hbρ (fun i => c (i, j) s)
    (col_majorant c ρ H hρ hc j s) J hJ).2]

/-- **The canonical `u`-face coefficient is an explicit absolutely convergent series**:
`U_{α_i}(s) = k₁⁻¹ ∑_j c_{ij}(s) · axisPrim γ_i b j`, `γ_i = k₂ α_i − h₂ − 1`. -/
theorem canonU_anaFaceU_series (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (h₁ h₂ k₁ k₂ : ℕ)
    (hb : 0 < b) (hbρ : b < ρ) (hk₁ : 0 < k₁)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (i : ℕ) :
    canonU b h₁ h₂ k₁ k₂ (anaFaceU c b) (fun i j s => c (i, j) s) (uExp h₁ k₁ i)
      = fun s => 1 / (k₁ : ℝ)
          * ∑' j : ℕ, c (i, j) s * axisPrim ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b j := by
  rw [canonU_uExp b h₁ h₂ k₁ k₂ hk₁ _ _ i]
  funext s
  exact faceFPCoeff_anaFaceU_series c b ρ _ H hb hbρ hc k₁ i _ (lt_canonicalM _) s

theorem canonV_anaFaceV_series (c : ℕ × ℕ → ℝ → ℝ) (b ρ : ℝ) (H : ℝ → ℝ) (h₁ h₂ k₁ k₂ : ℕ)
    (hb : 0 < b) (hbρ : b < ρ) (hk₂ : 0 < k₂)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (j : ℕ) :
    canonV b h₁ h₂ k₁ k₂ (anaFaceV c b) (fun i j s => c (i, j) s) (vExp h₂ k₂ j)
      = fun s => 1 / (k₂ : ℝ)
          * ∑' i : ℕ, c (i, j) s * axisPrim ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b i := by
  rw [canonV_vExp b h₁ h₂ k₁ k₂ hk₂ _ _ j]
  funext s
  exact faceFPCoeff_anaFaceV_series c b ρ _ H hb hbρ hc k₂ j _ (lt_canonicalM _) s

end Laplace.Grammar
