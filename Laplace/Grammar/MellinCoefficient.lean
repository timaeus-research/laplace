/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonomialAmplitudeAsymptotic
import Laplace.Grammar.HeadlinePhase

/-!
# The leading Mellin (zeta) coefficient of a normal-crossing amplitude

Unit 222 (Astra #24, optional programme E2). The paper evaluates normal moments through the zeta
function `ζ(z) = ∫ (u^{2k})^z η(u) u^h du` (transform of `K = u^{2k}`); for `η = 1` (paper's bare
case, `b = 1`) `ζ(z) = ∏ᵢ 1/(2kᵢz+hᵢ+1)` has a pole of order `m` at `z = -λ` with leading Laurent
coefficient `a_{-m} = ∏_{i∈J} 1/(2kᵢ) · ∏_{i∉J} 1/(hᵢ+1-2kᵢλ)` (eq. `a_minus_m_explicit`). We prove
the **real-axis Abelian limit corresponding to this leading coefficient** for an amplitude `η`
extending continuously to the closed cube (Lean: `η` continuous on `ℝ^d`):
```
s^m ∫_{(0,1]^d} η(u) ∏ᵢ uᵢ^{2kᵢ(-λ+s)+hᵢ} du → ∏_{J} 1/(2kᵢ) · ∫ η(πu) ∏_{i∉J} uᵢ^{hᵢ-2kᵢλ} du
```
as `s → 0⁺` (`mellin_leading_tendsto`), where `π` zeroes the minimising coordinates. The proof is
the monomial-moment transfer of `ContinuousMomentTransfer` (as for the Laplace-side amplitude
theorem), with the closed forms `∫₀¹ u^a du = 1/(a+1)` as the only analytic input: on each
minimising coordinate the measure `(2kᵢ s) u^{2kᵢ s - 1} du` has mass one and concentrates at `0`.
The statement does not assume that `λ` is attained: if no coordinate attains it, `m = 0`, `π = id`,
and the limit is the regular value at `-λ`. For general `η` the limit does not establish
meromorphic continuation or the exact pole order (the coefficient may vanish). For `η = 1` the
limit is the paper's `a_{-m}` (`mellinCoeff_one`); in the equal-ratio case it is `η(0) ∏ 1/(2kᵢ)`
(`mellinCoeff_equal`); and, by a definitional identity, the Laplace-side leading coefficient of
Headline VIII equals `Γ(λ) β^{-λ}/(m-1)!` times the Mellin coefficient
(`amplitudeCoeff_eq_gamma_mul_mellinCoeff`) — under the hypotheses of the Laplace amplitude theorem
(attained minimum, `β > 0`) the two independently proved Abelian limits thus recover the paper's
"single `Γ(λ)` factor from the Laplace–Tauberian passage", with no Tauberian theorem, meromorphic
continuation or pole theorem involved. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Laplace.Grammar

/-- `∏_{i∈J} 1/(2kᵢ)`: the Mellin face constant. -/
noncomputable def mellinConst {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) : ℝ :=
  ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1

/-- The leading Mellin coefficient of a continuous amplitude:
`∏_{J} 1/(2kᵢ) ∫ η(πu) ∏_{i∉J} uᵢ^{hᵢ-2kᵢλ} du`. -/
noncomputable def mellinCoeff {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (η : (Fin d → ℝ) → ℝ) : ℝ :=
  mellinConst h k l * ∫ u in unitBox d, η (faceProj h k l u) * residualWeight h k l u

/-- The exponent `2kᵢ(-λ + 1/N) + hᵢ` at `s = 1/N`. -/
noncomputable def mellinExp {d : ℕ} (h k : Fin d → ℕ) (l N : ℝ) (i : Fin d) : ℝ :=
  2 * (k i : ℝ) * (-l + 1 / N) + h i

/-- The Mellin weight at `s = 1/N`: `N^{-m} ∏ᵢ uᵢ^{2kᵢ(-λ+1/N)+hᵢ}`. -/
noncomputable def mellinWeight {d : ℕ} (h k : Fin d → ℕ) (l N : ℝ) (u : Fin d → ℝ) : ℝ :=
  if 0 < N then (∏ i, u i ^ mellinExp h k l N i) / N ^ multCount (ratioExp h k) l else 0

theorem mellinExp_eq_of_eq {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l N : ℝ) (i : Fin d)
    (hi : ratioExp h k i = l) : mellinExp h k l N i = -1 + 2 * (k i : ℝ) / N := by
  unfold mellinExp
  unfold ratioExp at hi
  have hk' : (0 : ℝ) < k i := by exact_mod_cast hk i
  have : 2 * (k i : ℝ) * l = h i + 1 := by
    rw [← hi]
    field_simp
  linear_combination -this

theorem mellinExp_gt {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l N : ℝ) (hN : 0 < N)
    (hmin : ∀ i, l ≤ ratioExp h k i) (i : Fin d) : -1 < mellinExp h k l N i := by
  unfold mellinExp
  have hk' : (0 : ℝ) < k i := by exact_mod_cast hk i
  have h1 : 2 * (k i : ℝ) * l ≤ h i + 1 := by
    have := hmin i
    unfold ratioExp at this
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  have h2 : 0 < 2 * (k i : ℝ) * (1 / N) := by positivity
  nlinarith

theorem mellinWeight_integrableOn {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l N : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) :
    IntegrableOn (mellinWeight h k l N) (unitBox d) := by
  unfold IntegrableOn mellinWeight
  by_cases hN : 0 < N
  · simp only [if_pos hN]
    rw [restrict_unitBox]
    exact (Integrable.fintype_prod_dep (f := fun i (t : ℝ) => t ^ mellinExp h k l N i) fun i =>
      integrableOn_Ioc_rpow_factor _ (mellinExp_gt h k hk l N hN hmin i)).div_const _
  · simp only [if_neg hN]
    exact integrable_zero _ _ _

theorem mellinWeight_nonneg {d : ℕ} (h k : Fin d → ℕ) (l N : ℝ) (u : Fin d → ℝ)
    (hu : u ∈ unitBox d) : 0 ≤ mellinWeight h k l N u := by
  unfold mellinWeight
  split_ifs with hN
  · refine div_nonneg (Finset.prod_nonneg fun i _ => ?_) (by positivity)
    exact Real.rpow_nonneg (hu i (Set.mem_univ i)).1.le _
  · exact le_rfl

/-- The per-coordinate factor of a monomial moment of the Mellin weight. -/
noncomputable def mellinFactor {d : ℕ} (h k : Fin d → ℕ) (l N : ℝ) (γ : Fin d → ℕ) (i : Fin d) :
    ℝ :=
  1 / ((γ i : ℝ) + mellinExp h k l N i + 1) / (if ratioExp h k i = l then N else 1)

theorem prod_ite_N {d : ℕ} (h k : Fin d → ℕ) (l N : ℝ) :
    (∏ i, if ratioExp h k i = l then N else (1 : ℝ)) = N ^ multCount (ratioExp h k) l := by
  rw [← Finset.prod_filter (fun i => ratioExp h k i = l) (fun _ => N), Finset.prod_const,
    multCount_eq_card]

/-- **Monomial moments of the Mellin weight** (closed form). -/
theorem integral_monomial_mellinWeight {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l N : ℝ)
    (hN : 0 < N) (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin d → ℕ) :
    ∫ u in unitBox d, (∏ i, u i ^ γ i) * mellinWeight h k l N u =
      ∏ i, mellinFactor h k l N γ i := by
  have hpt : ∀ u ∈ unitBox d, (∏ i, u i ^ γ i) * mellinWeight h k l N u =
      (∏ i, u i ^ ((γ i : ℝ) + mellinExp h k l N i)) / N ^ multCount (ratioExp h k) l := by
    intro u hu
    unfold mellinWeight
    rw [if_pos hN, ← mul_div_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have hu0 : 0 < u i := (hu i (Set.mem_univ i)).1
    rw [← Real.rpow_natCast, ← Real.rpow_add hu0]
  rw [setIntegral_congr_fun (measurableSet_unitBox d) hpt, integral_div, restrict_unitBox,
    integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => t ^ ((γ i : ℝ) + mellinExp h k l N i))]
  have hfactor : ∀ i, (∫ t in Ioc (0 : ℝ) 1, t ^ ((γ i : ℝ) + mellinExp h k l N i)) =
      1 / ((γ i : ℝ) + mellinExp h k l N i + 1) := fun i => by
    rw [integral_Ioc_rpow_factor]
    have := mellinExp_gt h k hk l N hN hmin i
    linarith [(Nat.cast_nonneg (γ i) : (0 : ℝ) ≤ γ i)]
  simp_rw [hfactor]
  unfold mellinFactor
  simp only [Finset.prod_div_distrib]
  rw [prod_ite_N]

/-- The limit of a per-coordinate factor. -/
noncomputable def mellinFactorLim {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (γ : Fin d → ℕ) (i : Fin d) :
    ℝ :=
  if ratioExp h k i = l then (if γ i = 0 then 1 / (2 * (k i : ℝ)) else 0)
  else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l)

theorem mellinFactor_tendsto {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin d → ℕ) (i : Fin d) :
    Tendsto (fun N => mellinFactor h k l N γ i) atTop (𝓝 (mellinFactorLim h k l γ i)) := by
  have hk' : (0 : ℝ) < k i := by exact_mod_cast hk i
  have hinv : Tendsto (fun N : ℝ => 2 * (k i : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  unfold mellinFactor mellinFactorLim
  by_cases hi : ratioExp h k i = l
  · simp only [if_pos hi]
    have hexp : ∀ N, mellinExp h k l N i = -1 + 2 * (k i : ℝ) / N := fun N =>
      mellinExp_eq_of_eq h k hk l N i hi
    simp_rw [hexp]
    by_cases hγ : γ i = 0
    · simp only [hγ, Nat.cast_zero, if_true]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
      rw [show (0 : ℝ) + (-1 + 2 * (k i : ℝ) / N) + 1 = 2 * (k i : ℝ) / N by ring]
      field_simp
    · simp only [if_neg hγ]
      have hγ' : (0 : ℝ) < γ i := by exact_mod_cast Nat.pos_of_ne_zero hγ
      have h1 : Tendsto (fun N : ℝ => 1 / ((γ i : ℝ) + (-1 + 2 * (k i : ℝ) / N) + 1)) atTop
          (𝓝 (1 / ((γ i : ℝ) + (-1 + 0) + 1))) :=
        tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_nhds.add hinv)
          |>.add tendsto_const_nhds) (by
            rw [show (γ i : ℝ) + (-1 + 0) + 1 = γ i by ring]; exact_mod_cast hγ)
      exact h1.div_atTop tendsto_id
  · simp only [if_neg hi, div_one]
    unfold mellinExp
    have hden : (h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l ≠ 0 := by
      have := residual_exponent_gt h k hk l hmin i hi
      have : (0 : ℝ) ≤ γ i := Nat.cast_nonneg _
      linarith
    have h1 : Tendsto (fun N : ℝ => 1 / ((γ i : ℝ) + (2 * (k i : ℝ) * (-l + 1 / N) + h i) + 1))
        atTop (𝓝 (1 / ((γ i : ℝ) + (2 * (k i : ℝ) * (-l + 0) + h i) + 1))) := by
      refine tendsto_const_nhds.div ?_ (by rw [show (γ i : ℝ) + (2 * (k i : ℝ) * (-l + 0) + h i) + 1
        = (h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l by ring]; exact hden)
      have hN' : Tendsto (fun N : ℝ => 1 / N) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      exact ((tendsto_const_nhds.mul (tendsto_const_nhds.add hN')).add tendsto_const_nhds)
        |>.const_add _ |>.add tendsto_const_nhds
    refine h1.congr' (Eventually.of_forall fun N => rfl) |>.trans ?_
    rw [show (γ i : ℝ) + (2 * (k i : ℝ) * (-l + 0) + h i) + 1 =
      (h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l by ring]

/-- **Face moments of the Mellin functional**: `γ = 0` on `J`. -/
theorem mellin_face_moment_eq {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin d → ℕ) (hγ : ∀ i, ratioExp h k i = l → γ i = 0) :
    ∫ u in unitBox d, (∏ i, faceProj h k l u i ^ γ i) * (mellinConst h k l * residualWeight h k l u)
      = ∏ i, mellinFactorLim h k l γ i := by
  have hpt : ∀ u ∈ unitBox d,
      (∏ i, faceProj h k l u i ^ γ i) * (mellinConst h k l * residualWeight h k l u) =
        mellinConst h k l * ∏ i, (if ratioExp h k i = l then (1 : ℝ)
          else u i ^ ((h i : ℝ) + γ i - 2 * (k i : ℝ) * l)) := by
    intro u hu
    unfold residualWeight faceProj
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [hγ i hi, pow_zero, one_mul]
    · have hu0 : 0 < u i := (hu i (Set.mem_univ i)).1
      rw [← Real.rpow_natCast, ← Real.rpow_add hu0]
      congr 1
      ring
  rw [setIntegral_congr_fun (measurableSet_unitBox d) hpt, integral_const_mul, restrict_unitBox,
    integral_fintype_prod_eq_prod (f := fun i (t : ℝ) =>
      if ratioExp h k i = l then (1 : ℝ) else t ^ ((h i : ℝ) + γ i - 2 * (k i : ℝ) * l))]
  have hfactor : ∀ i, (∫ t in Ioc (0 : ℝ) 1, if ratioExp h k i = l then (1 : ℝ)
      else t ^ ((h i : ℝ) + γ i - 2 * (k i : ℝ) * l)) =
      if ratioExp h k i = l then 1 else 1 / ((h i : ℝ) + γ i + 1 - 2 * (k i : ℝ) * l) := by
    intro i
    split_ifs with hi
    · simp
    · have ha : -1 < (h i : ℝ) + γ i - 2 * (k i : ℝ) * l := by
        have := residual_exponent_gt h k hk l hmin i hi
        linarith [(Nat.cast_nonneg (γ i) : (0 : ℝ) ≤ γ i)]
      rw [integral_Ioc_rpow_factor _ ha]
      ring_nf
  simp_rw [hfactor]
  unfold mellinConst mellinFactorLim
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : ratioExp h k i = l
  · rw [if_pos hi, if_pos hi, if_pos hi, if_pos (hγ i hi), mul_one]
  · rw [if_neg hi, if_neg hi, if_neg hi, one_mul]

/-- **Face moments of the Mellin functional**: a monomial touching `J` has zero moment. -/
theorem mellin_face_moment_eq_zero {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (γ : Fin d → ℕ)
    (hγ : ∃ j, ratioExp h k j = l ∧ γ j ≠ 0) :
    ∫ u in unitBox d, (∏ i, faceProj h k l u i ^ γ i) * (mellinConst h k l * residualWeight h k l u)
      = ∏ i, mellinFactorLim h k l γ i := by
  obtain ⟨j, hj, hγj⟩ := hγ
  have hL : ∏ i, mellinFactorLim h k l γ i = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    unfold mellinFactorLim
    rw [if_pos hj, if_neg hγj]
  rw [hL]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  have : faceProj h k l u j ^ γ j = 0 := by
    simp only [faceProj, if_pos hj]
    exact zero_pow hγj
  change (∏ i, faceProj h k l u i ^ γ i) * (mellinConst h k l * residualWeight h k l u) = 0
  rw [Finset.prod_eq_zero (Finset.mem_univ j) this, zero_mul]

/-- **Leading Mellin coefficient along `N = 1/s → ∞`.** -/
theorem mellinWeight_tendsto (d : ℕ) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) (η : (Fin d → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => ∫ u in unitBox d, η u * mellinWeight h k l N u) atTop
      (𝓝 (mellinCoeff h k l η)) := by
  have hT := tendsto_integral_of_monomials d (unitBox d) (measurableSet_unitBox _)
    (fun _ => id) (faceProj h k l) (fun _ => fun x hx => unitBox_subset_closedCube _ hx)
    (faceProj_mapsTo h k l) (fun _ => measurable_id) (measurable_faceProj h k l)
    (fun N => mellinWeight h k l N) (fun u => mellinConst h k l * residualWeight h k l u)
    (fun N => mellinWeight_integrableOn h k hk l N hmin)
    ((residualWeight_integrableOn h k hk l hmin).const_mul _)
    (Eventually.of_forall fun N x hx => mellinWeight_nonneg h k l N x hx)
    (fun u hu => mul_nonneg (Finset.prod_nonneg fun i _ => by
      split_ifs <;> positivity) (residualWeight_nonneg h k l u hu))
    (fun γ => ?_) η hη
  · unfold mellinCoeff
    rw [← integral_const_mul]
    have hlim : ∫ x in unitBox d, η (faceProj h k l x) *
        (mellinConst h k l * residualWeight h k l x) =
        ∫ x in unitBox d, mellinConst h k l * (η (faceProj h k l x) * residualWeight h k l x) :=
      setIntegral_congr_fun (measurableSet_unitBox _) fun x _ => by ring
    rw [hlim] at hT
    exact hT
  · simp only [id]
    have hlim : Tendsto (fun N => ∏ i, mellinFactor h k l N γ i) atTop
        (𝓝 (∏ i, mellinFactorLim h k l γ i)) :=
      tendsto_finsetProd _ fun i _ => mellinFactor_tendsto h k hk l hmin γ i
    by_cases hγ : ∀ i, ratioExp h k i = l → γ i = 0
    · rw [mellin_face_moment_eq h k hk l hmin γ hγ]
      refine hlim.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
      exact (integral_monomial_mellinWeight h k hk l N hN hmin γ).symm
    · push Not at hγ
      rw [mellin_face_moment_eq_zero h k l γ hγ]
      refine hlim.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
      exact (integral_monomial_mellinWeight h k hk l N hN hmin γ).symm

/-- **E2 — leading Mellin coefficient (Abelian form).**
`s^m ∫_{(0,1]^d} η(u) ∏ᵢ uᵢ^{2kᵢ(-λ+s)+hᵢ} du → ∏_{J} 1/(2kᵢ) ∫ η(πu) ∏_{i∉J} uᵢ^{hᵢ-2kᵢλ} du` as
`s → 0⁺`. -/
theorem mellin_leading_tendsto (d : ℕ) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) (η : (Fin d → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun s : ℝ => s ^ multCount (ratioExp h k) l *
      ∫ u in unitBox d, η u * ∏ i, u i ^ (2 * (k i : ℝ) * (-l + s) + h i)) (𝓝[>] 0)
      (𝓝 (mellinCoeff h k l η)) := by
  have h1 := (mellinWeight_tendsto d h k hk l hmin η hη).comp tendsto_inv_nhdsGT_zero
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_unitBox d) fun u _ => ?_
  unfold mellinWeight mellinExp
  have hs' : (0 : ℝ) < s := hs
  rw [if_pos (inv_pos.2 hs'), one_div, inv_inv, inv_pow, div_eq_mul_inv, inv_inv]
  ring

/-- For `η = 1` the Mellin coefficient is the paper's `a_{-m}` at `b = 1`:
`∏_{J} 1/(2kᵢ) · ∏_{i∉J} 1/(hᵢ+1-2kᵢλ)`. -/
theorem mellinCoeff_one (d : ℕ) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) :
    mellinCoeff h k l (fun _ => 1) = ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ))
      else 1 / ((h i : ℝ) + 1 - 2 * (k i : ℝ) * l) := by
  have h0 := mellin_face_moment_eq h k hk l hmin (fun _ => 0) (fun _ _ => rfl)
  simp only [pow_zero, Finset.prod_const_one, one_mul] at h0
  unfold mellinCoeff
  simp only [one_mul]
  rw [← integral_const_mul, h0]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold mellinFactorLim
  by_cases hi : ratioExp h k i = l
  · simp [hi]
  · simp [hi]

/-- Equal ratios: the Mellin coefficient is the corner value `η(0) ∏ᵢ 1/(2kᵢ)`. -/
theorem mellinCoeff_equal (d : ℕ) (h k : Fin d → ℕ) (l : ℝ) (hratio : ∀ i, ratioExp h k i = l)
    (η : (Fin d → ℝ) → ℝ) : mellinCoeff h k l η = η 0 * ∏ i, 1 / (2 * (k i : ℝ)) := by
  have hπ : faceProj h k l = fun _ => 0 := by
    funext u i
    simp [faceProj, hratio]
  have hw : residualWeight h k l = fun _ => 1 := by
    funext u
    unfold residualWeight
    simp [hratio]
  unfold mellinCoeff mellinConst
  rw [hπ, hw]
  simp only [mul_one]
  rw [setIntegral_const, measureReal_def, volume_unitBox, ENNReal.toReal_one, one_smul,
    Finset.prod_congr rfl fun i _ => if_pos (hratio i)]
  ring

/-- **Laplace–Mellin dictionary**: the Laplace-side leading coefficient of Headline VIII is
`Γ(λ) β^{-λ}/(m-1)!` times the Mellin coefficient — the paper's single `Γ(λ)` factor, here by
comparison of two Abelian limits. -/
theorem amplitudeCoeff_eq_gamma_mul_mellinCoeff {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ)
    (η : (Fin d → ℝ) → ℝ) :
    amplitudeCoeff h k l β η = Real.Gamma l * β ^ (-l) /
      ((multCount (ratioExp h k) l - 1).factorial : ℝ) * mellinCoeff h k l η := by
  unfold amplitudeCoeff faceLeadConst mellinCoeff mellinConst
  ring

end Laplace.Grammar
