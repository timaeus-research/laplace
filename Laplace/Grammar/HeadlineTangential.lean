/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TangentialAmplitude

/-!
# Headline statements, part IX: the local leading-density coefficient

Paper-facing wrappers for unit 189 (tangential integration of the normal block). For a compact
tangential set `K` with an integrable (signed) density `q`, a continuous amplitude `η(v,u)`, and
normal data `(hᵢ, kᵢ)` with Mellin ratios `ℓᵢ`, minimum `λ` attained on `J`:

* **mixed ratios** (`headline_tangential_normal_moment`): the tangentially integrated dressed normal
  moment, normalised by `N^{-λ}(log N)^{|J|-1}`, converges to
  `∫_K q(v) · Γ(λ)β^{-λ}/(|J|-1)! ∏_{j∈J} 1/(2kⱼ) ∫ η(v, P_J u) ∏_{i∉J} uᵢ^{hᵢ-2kᵢλ} du dv`;
* **equal ratios** (`headline_tangential_normal_moment_equal`): the limit is
  `Γ(λ)β^{-λ}/(m! ∏ᵢ 2kᵢ) · ∫_K q(v) η(v, 0) dv` for `m + 1` normal variables (the paper's
  `(m−1)!` counts `m` normal variables) — the deterministic chart-level precursor of the
  paper's leading coefficient `Γ(λ)/(m-1)! a_I ∫_{S_I} (φ∘π) c₀ |dv|` (eq. `thm_leading_coeff`),
  with the density `c₀` and the observable both absorbed into `q · η`;
* the **equivalence form** under a nonzero integrated coefficient
  (`headline_tangential_normal_moment_equiv`); tangential cancellation may kill the coefficient
  even when individual normal sections have nonzero coefficients.

Scope: one normal block in fixed coordinates; the identification of `∫_K q(v) … dv` with the
paper's stratum integral `∫_{S_I} c₀ |dv|` requires the chart/partition-of-unity bridge, which is
NOT claimed. Zero `sorry`/`axiom`.
-/

open Asymptotics Filter MeasureTheory Set Topology

namespace Laplace.Grammar

variable {t : ℕ}

/-- **Mixed ratios**: tangentially integrated dressed normal moment, face-supported coefficient. -/
theorem headline_tangential_normal_moment (m : ℕ) (h k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hmin : ∀ i, l ≤ ((h i : ℝ) + 1) / (2 * (k i : ℝ)))
    (hatt : ∃ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l)
    (K : Set (Fin t → ℝ)) (hKc : IsCompact K) (hK : MeasurableSet K) (q : (Fin t → ℝ) → ℝ)
    (hq : IntegrableOn q K) (η : (Fin t → ℝ) × (Fin (m + 1) → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => (∫ v in K, q v * ∫ x in unitBox (m + 1),
        η (v, x) * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) *
          Real.log N ^ ((∑ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 else 0) - 1)))
      atTop
      (𝓝 (∫ v in K, q v * ((Real.Gamma l * β ^ (-l) /
          (((∑ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 else 0) - 1).factorial : ℝ) *
          ∏ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 1 / (2 * (k i : ℝ)) else 1) *
        ∫ u in unitBox (m + 1),
          η (v, fun i => if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then 0 else u i) *
            ∏ i, if ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l then (1 : ℝ)
              else u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * l)))) :=
  tangential_amplitude_tendsto m h k hk l β hl hβ hmin hatt K hKc hK q hq η hη

/-- **Equal ratios**: the local leading-density coefficient
`Γ(λ)β^{-λ}/(m! ∏ᵢ 2kᵢ) · ∫_K q(v) η(v,0) dv`. -/
theorem headline_tangential_normal_moment_equal (m : ℕ) (h k : Fin (m + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β)
    (hratio : ∀ i, ((h i : ℝ) + 1) / (2 * (k i : ℝ)) = l)
    (K : Set (Fin t → ℝ)) (hKc : IsCompact K) (hK : MeasurableSet K) (q : (Fin t → ℝ) → ℝ)
    (hq : IntegrableOn q K) (η : (Fin t → ℝ) × (Fin (m + 1) → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => (∫ v in K, q v * ∫ x in unitBox (m + 1),
        η (v, x) * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) * Real.log N ^ m)) atTop
      (𝓝 ((Real.Gamma l * β ^ (-l) / ((m.factorial : ℝ) * ∏ i, 2 * (k i : ℝ))) *
        ∫ v in K, q v * η (v, 0))) := by
  have hm : multCount (ratioExp h k) l = m + 1 := by
    unfold multCount
    simp [ratioExp, hratio]
  have hT := tangential_amplitude_tendsto m h k hk l β hl hβ (fun i => (hratio i).symm.le)
    ⟨0, hratio 0⟩ K hKc hK q hq η hη
  rw [hm, Nat.add_sub_cancel] at hT
  have hc : ∫ v in K, q v * amplitudeCoeff h k l β (fun u => η (v, u)) =
      (Real.Gamma l * β ^ (-l) / ((m.factorial : ℝ) * ∏ i, 2 * (k i : ℝ))) *
        ∫ v in K, q v * η (v, 0) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    beta_reduce
    rw [amplitudeCoeff_equal m h k l β hratio]
    ring
  rw [hc] at hT
  exact hT

/-- **Equivalence form** under a nonzero integrated coefficient. -/
theorem headline_tangential_normal_moment_equiv (m : ℕ) (h k : Fin (m + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (K : Set (Fin t → ℝ)) (hKc : IsCompact K)
    (hK : MeasurableSet K) (q : (Fin t → ℝ) → ℝ) (hq : IntegrableOn q K)
    (η : (Fin t → ℝ) × (Fin (m + 1) → ℝ) → ℝ) (hη : Continuous η)
    (hc : (∫ v in K, q v * amplitudeCoeff h k l β (fun u => η (v, u))) ≠ 0) :
    (fun N => ∫ v in K, q v * ∫ x in unitBox (m + 1),
        η (v, x) * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) ~[atTop]
      fun N => (∫ v in K, q v * amplitudeCoeff h k l β (fun u => η (v, u))) * N ^ (-l) *
        Real.log N ^ (multCount (ratioExp h k) l - 1) := by
  refine isEquivalent_of_tendsto_one ?_
  have hT := (tangential_amplitude_tendsto m h k hk l β hl hβ hmin hatt K hKc hK q hq
    η hη).div_const (∫ v in K, q v * amplitudeCoeff h k l β (fun u => η (v, u)))
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
