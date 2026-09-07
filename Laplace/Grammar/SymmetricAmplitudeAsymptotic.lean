/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.SignedReflection

/-!
# Dressed normal moments on symmetric boxes: asymptotics and the parity headline

Second unit of the signed-reflection extension. Combining the exact reduction
`∫_{(-1,1]^d} η x^h e^{-βN x^{2k}} = ∫_{(0,1]^d} η_sym u^h e^{-βN u^{2k}}` (unit 196) with the
continuous-amplitude theorem (unit 186):

* the symmetric-box dressed integral, normalised by `N^{-λ}(log N)^{|J|-1}`, converges to the face
  coefficient of `η_sym` (`symmetric_amplitude_tendsto`);
* for equal ratios the limit is `η(0) ∏ᵢ(1+(-1)^{hᵢ}) · Γ(λ)β^{-λ}/(m! ∏ᵢ 2kᵢ)`
  (`symmetric_amplitude_equal`), so **an odd exponent annihilates the equal-ratio leading corner
  coefficient** (`symmetric_amplitude_odd`): the integral is then `o(N^{-λ}(log N)^m)`; it need not
  vanish identically (it may, e.g. for a constant amplitude), and no next-order rate is claimed.

Headline wrappers (part XI) restate these on the Bochner integrals.
-/

open MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- **Symmetric-box dressed asymptotic**: the face coefficient of the signed symmetrisation. -/
theorem symmetric_amplitude_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (η : (Fin (d + 1) → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => (∫ x in symBox (d + 1),
        η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (amplitudeCoeff h k l β (symAmp h η))) := by
  have hT := amplitude_tendsto d h k hk l β hl hβ hmin hatt (symAmp h η) (continuous_symAmp h η hη)
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  beta_reduce
  rw [integral_symBox_eq_symAmp β (d + 1) h k N η hη]

/-- **Equal ratios**: the corner coefficient picks up the parity product. -/
theorem symmetric_amplitude_equal (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hratio : ∀ i, ratioExp h k i = l)
    (η : (Fin (m + 1) → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => (∫ x in symBox (m + 1),
        η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) * Real.log N ^ m)) atTop
      (𝓝 (η 0 * (∏ i, (1 + (-1 : ℝ) ^ h i)) *
        (Real.Gamma l * β ^ (-l) / ((m.factorial : ℝ) * ∏ i, 2 * (k i : ℝ))))) := by
  have hm : multCount (ratioExp h k) l = m + 1 := by
    unfold multCount
    simp [hratio]
  have hT := symmetric_amplitude_tendsto m h k hk l β hl hβ (fun i => (hratio i).symm.le)
    ⟨0, hratio 0⟩ η hη
  rw [hm, Nat.add_sub_cancel, amplitudeCoeff_equal m h k l β hratio, symAmp_zero] at hT
  exact hT

/-- **Odd exponent, equal ratios**: the leading corner coefficient vanishes, so the symmetric-box
dressed integral is `o(N^{-λ}(log N)^m)`. -/
theorem symmetric_amplitude_odd (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hratio : ∀ i, ratioExp h k i = l) (j : Fin (m + 1))
    (hodd : Odd (h j)) (η : (Fin (m + 1) → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => (∫ x in symBox (m + 1),
        η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) * Real.log N ^ m)) atTop (𝓝 0) := by
  have hT := symmetric_amplitude_equal m h k hk l β hl hβ hratio η hη
  have hzero : (∏ i, (1 + (-1 : ℝ) ^ h i)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hodd.neg_one_pow]; norm_num)
  rw [hzero, mul_zero, zero_mul] at hT
  exact hT

/-- **Headline XI**: dressed normal moments on the symmetric box `(-1,1]^{m+1}` with a continuous
amplitude — the face coefficient of the signed symmetrisation. -/
theorem headline_symmetric_normal_moment_amplitude (m : ℕ) (h k : Fin (m + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hmin : ∀ i, l ≤ ((h i : ℝ) + 1) / (2 * (k i : ℝ)))
    (hatt : ∃ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) (η : (Fin (m + 1) → ℝ) → ℝ)
    (hη : Continuous η) :
    Tendsto (fun N => (∫ x in symBox (m + 1),
        η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (amplitudeCoeff h k l β fun u =>
        ∑ σ : Fin (m + 1) → Bool, (∏ i, sgn (σ i) ^ h i) * η (reflect σ u))) :=
  symmetric_amplitude_tendsto m h k hk l β hl hβ hmin hatt η hη

/-- **Headline XI, equal ratios**: `η(0) ∏ᵢ(1+(-1)^{hᵢ}) · Γ(λ)β^{-λ}/(m! ∏ᵢ 2kᵢ)`; an odd exponent
kills the corner coefficient. -/
theorem headline_symmetric_normal_moment_equal (m : ℕ) (h k : Fin (m + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l) (η : (Fin (m + 1) → ℝ) → ℝ)
    (hη : Continuous η) :
    Tendsto (fun N => (∫ x in symBox (m + 1),
        η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) * Real.log N ^ m)) atTop
      (𝓝 (η 0 * (∏ i, (1 + (-1 : ℝ) ^ h i)) *
        (Real.Gamma l * β ^ (-l) / ((m.factorial : ℝ) * ∏ i, 2 * (k i : ℝ))))) :=
  symmetric_amplitude_equal m h k hk l β hl hβ hratio η hη

end Laplace.Grammar
