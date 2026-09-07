/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.JetRemainder

/-!
# The all-order expansion of the one-dimensional chart integral (grammar §4.2)

For a chart amplitude `η(u) e^{βsξ(u)}` with `ξ, η` admitting order-`R` Taylor expansions at
`u = 0` and `ξ` Lipschitz at `0`, the scaled integral
`∫₀^b u^h e^{-β(Nu^k)²} η(u) e^{β(Nu^k)ξ(u)} du` has the expansion

  `∑_{j<R} c_j N^{-(p + j/k)} + O(N^{-(p+R/k)})`,   `p = (h+1)/k`,

with `c_j = k⁻¹ ∫₀^∞ s^{p+j/k-1} e^{-βs²} e^{βs x₀} P_j(s) ds` (`jetCoeff` of `chartJet`), and the
polynomial `P_j` integrates termwise to a finite combination of the weighted masses
`S_λ(x₀) = ∫ s^{λ-1} e^{-βs² + βx₀ s}`:

  `c_j = k⁻¹ ∑_{m<R} (β^m/m!) e_{j,m} S_{p+j/k+m}(x₀)`,   `e_{j,m} = ∑_{ℓ≤j} y_ℓ [u^{j-ℓ}](g_R^m)`.

`oneDChart_all_orders` is the all-order 1D theorem; `jetCoeff_chartJet_eq` is the closed form of
its coefficients. Zero `sorry`/`axiom`.
-/

open Real Finset MeasureTheory Set

namespace Laplace.Grammar

/-- Moment integrability against a `(1+s)^R e^{βsa'}` envelope. -/
theorem moment_integrableOn_of_envelope (β a' γ A : ℝ) (hβ : 0 < β) (hγ : -1 < γ) (j R : ℕ)
    (c : ℝ → ℝ) (hc : Measurable c)
    (hbound : ∀ s, 0 < s → |c s| ≤ A * (1 + s) ^ R * Real.exp (β * s * a')) :
    IntegrableOn (fun s => s ^ γ * (1 + |Real.log s|) ^ j * (Real.exp (-β * s ^ 2) * |c s|))
      (Ioi 0) := by
  have hdom : IntegrableOn (fun s : ℝ => ∑ m ∈ range (R + 1),
      A * (R.choose m : ℝ) * ((1 + |Real.log s|) ^ j * (s ^ (γ + m) * quadKernel β a' s)))
      (Ioi 0) := by
    refine integrable_finsetSum _ fun m _ => ?_
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact (logPowShift_weightedKernel_integrableOn β a' (γ + m) 1 hβ (by linarith) j).const_mul _
  refine Integrable.mono' hdom ?_ ?_
  · exact (((measurable_id.pow_const _).mul ((measurable_const.add
      (continuous_abs.measurable.comp Real.measurable_log)).pow_const _)).mul
      ((Real.measurable_exp.comp (measurable_const.mul (measurable_id.pow_const _))).mul
        (continuous_abs.measurable.comp hc))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs
    have hsγ : 0 ≤ s ^ γ := Real.rpow_nonneg hs0.le _
    have hL : 0 ≤ (1 + |Real.log s|) ^ j := pow_nonneg (by positivity) _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg hsγ hL) (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)))]
    have hq : Real.exp (-β * s ^ 2) * Real.exp (β * s * a') = quadKernel β a' s :=
      exp_mul_exp_eq_quadKernel β a' s
    have hE : 0 ≤ Real.exp (-β * s ^ 2) := (Real.exp_pos _).le
    calc s ^ γ * (1 + |Real.log s|) ^ j * (Real.exp (-β * s ^ 2) * |c s|)
        ≤ s ^ γ * (1 + |Real.log s|) ^ j
          * (Real.exp (-β * s ^ 2) * (A * (1 + s) ^ R * Real.exp (β * s * a'))) := by
          gcongr
          exact hbound s hs0
      _ = A * ((1 + |Real.log s|) ^ j * (s ^ γ * quadKernel β a' s)) * (s + 1) ^ R := by
          rw [← hq]; ring
      _ = A * ((1 + |Real.log s|) ^ j * (s ^ γ * quadKernel β a' s))
          * ∑ m ∈ range (R + 1), s ^ m * 1 ^ (R - m) * (R.choose m : ℝ) := by rw [add_pow s 1 R]
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Real.rpow_add hs0, Real.rpow_natCast, one_pow, mul_one]
          ring

/-- The amplitude jet is bounded by a `(1+s)^R` envelope. -/
theorem ampJet_abs_le (β : ℝ) (hβ : 0 < β) (x y : ℕ → ℝ) (R j : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    |ampJet β x y R j s|
      ≤ (∑ ℓ ∈ range (j + 1), |y ℓ| * expJetConst β x R (j - ℓ)) * (1 + s) ^ R := by
  unfold ampJet
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ℓ _ => ?_)
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (expJet_abs_le β hβ x R _ s hs) (abs_nonneg _)

/-- The jet coefficients of the chart amplitude, `F_j(s) = e^{βs x₀} P_j(s)`. -/
noncomputable def chartJet (β : ℝ) (x y : ℕ → ℝ) (R j : ℕ) (s : ℝ) : ℝ :=
  Real.exp (β * s * x 0) * ampJet β x y R j s

theorem chartJet_continuous (β : ℝ) (x y : ℕ → ℝ) (R j : ℕ) : Continuous (chartJet β x y R j) := by
  unfold chartJet
  exact (Real.continuous_exp.comp (by fun_prop)).mul (ampJet_continuous β x y R j)

theorem chartJet_abs_le (β : ℝ) (hβ : 0 < β) (x y : ℕ → ℝ) (R j : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    |chartJet β x y R j s|
      ≤ (∑ ℓ ∈ range (j + 1), |y ℓ| * expJetConst β x R (j - ℓ)) * (1 + s) ^ R
        * Real.exp (β * s * x 0) := by
  unfold chartJet
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (ampJet_abs_le β hβ x y R j s hs) (Real.exp_pos _).le

/-- **The all-order expansion of the 1D chart integral.** For `ξ, η` with order-`R` Taylor
expansions at `0` on `[0,b]` and `ξ` Lipschitz at `0`,
`∫₀^b u^h e^{-β(Nu^k)²} η(u) e^{β(Nu^k)ξ(u)} du = ∑_{j<R} c_j N^{-(p+j/k)} + O(N^{-(p+R/k)})`
with `c_j = jetCoeff β p k (chartJet β x y R) j`. -/
theorem oneDChart_all_orders (β b K L₁ p : ℝ) (h k R : ℕ) (hβ : 0 < β) (hb : 0 < b) (hK : 0 ≤ K)
    (hL₁ : 0 ≤ L₁) (hk : 0 < k) (hp : ((h : ℝ) + 1) / k = p) (hR : 0 < R)
    (x y : ℕ → ℝ) (ξ η : ℝ → ℝ) (hξm : Measurable ξ) (hηm : Measurable η)
    (hξT : ∀ u ∈ Set.Icc (0 : ℝ) b, |ξ u - ∑ i ∈ range R, x i * u ^ i| ≤ K * u ^ R)
    (hηT : ∀ u ∈ Set.Icc (0 : ℝ) b, |η u - ∑ i ∈ range R, y i * u ^ i| ≤ K * u ^ R)
    (hξL : ∀ u ∈ Set.Icc (0 : ℝ) b, |ξ u - x 0| ≤ L₁ * u) :
    ∃ K' : ℝ, ∀ N : ℝ, 1 ≤ N →
      |oneDScale β b N h k ξ η
          - ∑ j ∈ range R, jetCoeff β p k (chartJet β x y R) j * N ^ (-(p + (j : ℝ) / k))|
        ≤ K' * N ^ (-(p + (R : ℝ) / k)) := by
  obtain ⟨C, hC0, hC⟩ := amp_jet_remainder β b K L₁ hβ hb hK hL₁ x y R hR ξ η hξT hηT hξL
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hp0 : 0 < p := by rw [← hp]; positivity
  set HR : ℝ → ℝ := fun s => C * (1 + |s|) ^ R * Real.exp (β * s * (x 0 + L₁ * b)) with hHR
  have hHm : Measurable HR := by
    rw [hHR]
    fun_prop
  have hH0 : ∀ s, 0 ≤ HR s := fun s => by
    simp only [hHR]
    positivity
  have hFm : Measurable (Function.uncurry fun u s => η u * Real.exp (β * s * ξ u)) :=
    (hηm.comp measurable_fst).mul (Real.measurable_exp.comp
      ((measurable_const.mul measurable_snd).mul (hξm.comp measurable_fst)))
  have hrem : ∀ u ∈ Icc (0 : ℝ) b, ∀ s, 0 < s →
      |η u * Real.exp (β * s * ξ u) - ∑ j ∈ range R, u ^ j * chartJet β x y R j s|
        ≤ u ^ R * HR s := by
    intro u hu s hs
    refine (hC u hu s hs.le).trans (le_of_eq ?_)
    simp only [hHR, abs_of_pos hs]
    ring
  have hMc : ∀ j, j < R → IntegrableOn (fun s => s ^ (p + (j : ℝ) / k - 1)
      * (1 + |Real.log s|) ^ 0 * (Real.exp (-β * s ^ 2) * |chartJet β x y R j s|)) (Ioi 0) := by
    intro j _
    have hjk : (0 : ℝ) ≤ (j : ℝ) / k := by positivity
    exact moment_integrableOn_of_envelope β (x 0) (p + (j : ℝ) / k - 1) _ hβ (by linarith) 0 R _
      (chartJet_continuous β x y R j).measurable fun s hs => chartJet_abs_le β hβ x y R j s hs.le
  have hMt : ∀ j, j < R → IntegrableOn (fun s => s ^ (p + (R : ℝ) / k - 1)
      * (1 + |Real.log s|) ^ 0 * (Real.exp (-β * s ^ 2) * |chartJet β x y R j s|)) (Ioi 0) := by
    intro j _
    have hRk : (0 : ℝ) ≤ (R : ℝ) / k := by positivity
    exact moment_integrableOn_of_envelope β (x 0) (p + (R : ℝ) / k - 1) _ hβ (by linarith) 0 R _
      (chartJet_continuous β x y R j).measurable fun s hs => chartJet_abs_le β hβ x y R j s hs.le
  have hMH : IntegrableOn (fun s => s ^ (p + (R : ℝ) / k - 1) * (1 + |Real.log s|) ^ 0
      * (Real.exp (-β * s ^ 2) * HR s)) (Ioi 0) := by
    have hRk : (0 : ℝ) ≤ (R : ℝ) / k := by positivity
    have this : IntegrableOn (fun s => s ^ (p + (R : ℝ) / k - 1) * (1 + |Real.log s|) ^ 0
        * (Real.exp (-β * s ^ 2) * |HR s|)) (Ioi 0) :=
      moment_integrableOn_of_envelope β (x 0 + L₁ * b) (p + (R : ℝ) / k - 1) C hβ (by linarith) 0 R
        HR hHm fun s hs => by rw [abs_of_nonneg (hH0 s)]; simp only [hHR]; rw [abs_of_pos hs]
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    beta_reduce
    rw [abs_of_nonneg (hH0 s)]
  obtain ⟨K', hK'⟩ := oneDKernel_jet_expansion β b p h k R (fun u s => η u * Real.exp (β * s * ξ u))
    (chartJet β x y R) HR hb hk hp hFm (fun j => (chartJet_continuous β x y R j).measurable)
    hHm hH0 hrem hMc hMt hMH
  refine ⟨K', fun N hN => ?_⟩
  rw [oneDScale_eq_oneDKernel]
  exact hK' N hN

/-- The mixed jet coefficients `e_{j,m} = ∑_{ℓ≤j} y_ℓ [u^{j-ℓ}](g_R^m)`. -/
noncomputable def chartJetCoeff (x y : ℕ → ℝ) (R j m : ℕ) : ℝ :=
  ∑ ℓ ∈ range (j + 1), y ℓ * ((gPoly x R) ^ m).coeff (j - ℓ)

/-- **Closed form of the all-order coefficients**:
`c_j = k⁻¹ ∑_{m<R} (β^m/m!) e_{j,m} S_{p+j/k+m}(x₀)` with `S_λ(a) = weightedMass β a (λ-1)`. -/
theorem jetCoeff_chartJet_eq (β p : ℝ) (k : ℕ) (hβ : 0 < β) (hp : 0 < p) (x y : ℕ → ℝ) (R j : ℕ) :
    jetCoeff β p k (chartJet β x y R) j
      = 1 / (k : ℝ) * ∑ m ∈ range R, β ^ m / (m.factorial : ℝ) * chartJetCoeff x y R j m
          * weightedMass β (x 0) (p + (j : ℝ) / k + m - 1) := by
  have hjk : (0 : ℝ) ≤ (j : ℝ) / k := by positivity
  unfold jetCoeff
  congr 1
  unfold logMoment weightedMass
  have hpt : ∀ s ∈ Ioi (0 : ℝ), s ^ (p + (j : ℝ) / k - 1) * Real.log s ^ 0
      * (Real.exp (-β * s ^ 2) * chartJet β x y R j s)
      = ∑ m ∈ range R, β ^ m / (m.factorial : ℝ) * chartJetCoeff x y R j m
          * (s ^ (p + (j : ℝ) / k + m - 1) * quadKernel β (x 0) s) := by
    intro s hs
    have hs0 : 0 < s := hs
    unfold chartJet ampJet expJet chartJetCoeff
    rw [pow_zero, mul_one, ← mul_assoc (Real.exp (-β * s ^ 2)), exp_mul_exp_eq_quadKernel]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun ℓ _ => ?_
    rw [show p + (j : ℝ) / k + m - 1 = (p + (j : ℝ) / k - 1) + (m : ℝ) by ring,
      Real.rpow_add hs0, Real.rpow_natCast, mul_pow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  rw [integral_finsetSum _ fun m _ => ?_]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul]
  · have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact (weightedKernel_integrableOn β (x 0) (p + (j : ℝ) / k + m - 1) hβ
      (by linarith)).const_mul _

end Laplace.Grammar
