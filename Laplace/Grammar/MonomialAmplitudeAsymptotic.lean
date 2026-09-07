/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.ContinuousMomentTransfer

/-!
# The dressed normal moment integral with a continuous amplitude

Assembly of the continuous-amplitude milestone (Astra #16, route C). For exponents
`h k : Fin (m+1) → ℕ`, `kᵢ > 0`, Mellin ratios `ℓᵢ = (hᵢ+1)/(2kᵢ)` with minimum `λ` attained on `J`,
and a continuous amplitude `η`, the dressed normal moment integral

  `I_η(N) = ∫_{(0,1]^{m+1}} η(x) x^h e^{-βN x^{2k}} dx`

satisfies

  `I_η(N) / (N^{-λ} (log N)^{|J|-1}) → Γ(λ) β^{-λ}/(|J|-1)! ∏_{j∈J} 1/(2kⱼ) ·
      ∫_{(0,1]^{m+1}} η(P_J u) ∏_{i∉J} uᵢ^{hᵢ-2kᵢλ} du`

(`amplitude_tendsto`), where `P_J` zeroes the minimal coordinates. The limiting functional is
**face-supported**: the amplitude is restricted to the face `u_J = 0` and integrated over the
nonminimal normal directions against the residual weight; the minimal coordinates integrate out
with mass one. Only when all ratios are equal does this reduce to `η(0)` times the bare constant.

Proof: the shifted monomial moments of unit 184 are the moments of this functional
(`face_moment_eq`, `face_moment_eq_zero`), and the moment-transfer theorem of unit 185 upgrades
monomial convergence to continuous test functions.
-/

open MeasureTheory Set Filter Topology

namespace Laplace.Grammar

/-- The projection onto the minimal face: zero the coordinates with ratio `λ`. -/
noncomputable def faceProj {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if ratioExp h k i = l then 0 else u i

/-- The residual weight `∏_{i∉J} uᵢ^{hᵢ - 2kᵢλ}` on the nonminimal coordinates. -/
noncomputable def residualWeight {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) : ℝ :=
  ∏ i, if ratioExp h k i = l then 1 else u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * l)

/-- The face constant `Γ(λ) β^{-λ}/(|J|-1)! ∏_{j∈J} 1/(2kⱼ)`. -/
noncomputable def faceLeadConst {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) : ℝ :=
  Real.Gamma l * β ^ (-l) / ((multCount (ratioExp h k) l - 1).factorial : ℝ) *
    ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1

/-- The face-supported leading functional applied to an amplitude. -/
noncomputable def amplitudeCoeff {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) (η : (Fin d → ℝ) → ℝ) : ℝ :=
  faceLeadConst h k l β * ∫ u in unitBox d, η (faceProj h k l u) * residualWeight h k l u

theorem faceProj_mapsTo {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) :
    MapsTo (faceProj h k l) (unitBox d) (closedCube d) := by
  intro u hu i _
  simp only [faceProj]
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨(hu i (mem_univ i)).1.le, (hu i (mem_univ i)).2⟩

theorem measurable_faceProj {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) : Measurable (faceProj h k l) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [faceProj]
  split_ifs
  · exact measurable_const
  · exact measurable_pi_apply i

/-- The residual exponents exceed `-1` on the nonminimal coordinates. -/
theorem residual_exponent_gt {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) (i : Fin d) (hi : ratioExp h k i ≠ l) :
    -1 < (h i : ℝ) - 2 * (k i : ℝ) * l := by
  have hlt : l < ratioExp h k i := lt_of_le_of_ne (hmin i) (Ne.symm hi)
  unfold ratioExp at hlt
  have hk0 : (0 : ℝ) < k i := by exact_mod_cast hk i
  rw [lt_div_iff₀ (by positivity)] at hlt
  linarith

/-- The one-dimensional factor integrals of the face functional. -/
theorem integral_Ioc_rpow_factor (a : ℝ) (ha : -1 < a) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ a = 1 / (a + 1) := by
  have := integral_Ioc_rpow_sub_one (a + 1) 1 (by linarith) zero_le_one
  simp only [add_sub_cancel_right, Real.one_rpow] at this
  rw [this]

theorem integrableOn_Ioc_rpow_factor (a : ℝ) (ha : -1 < a) :
    IntegrableOn (fun t : ℝ => t ^ a) (Ioc 0 1) := by
  have h := integrableOn_Ioc_rpow_gap 0 (a + 1) (by linarith)
  simpa using h

/-- The residual weight is integrable on the box. -/
theorem residualWeight_integrableOn {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) :
    IntegrableOn (residualWeight h k l) (unitBox d) := by
  unfold IntegrableOn residualWeight
  rw [restrict_unitBox]
  refine Integrable.fintype_prod_dep (f := fun i (t : ℝ) =>
    if ratioExp h k i = l then (1 : ℝ) else t ^ ((h i : ℝ) - 2 * (k i : ℝ) * l)) fun i => ?_
  split_ifs with hi
  · exact integrable_const _
  · exact integrableOn_Ioc_rpow_factor _ (residual_exponent_gt h k hk l hmin i hi)

theorem residualWeight_nonneg {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ)
    (hu : u ∈ unitBox d) : 0 ≤ residualWeight h k l u := by
  unfold residualWeight
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs
  · exact zero_le_one
  · exact Real.rpow_nonneg (hu i (mem_univ i)).1.le _

theorem faceLeadConst_pos {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ) (hl : 0 < l)
    (hβ : 0 < β) : 0 < faceLeadConst h k l β := by
  unfold faceLeadConst
  have h1 := Real.Gamma_pos_of_pos hl
  have h2 := Real.rpow_pos_of_pos hβ (-l)
  have h3 : 0 < ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else (1 : ℝ) :=
    Finset.prod_pos fun i _ => by split_ifs <;> [skip; exact one_pos]; have := hk i; positivity
  positivity

/-- **Face moments (face shifts)**: for `γ = 0` on `J`, the moment of the face functional is the
mixed constant of the shifted exponents. -/
theorem face_moment_eq {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin d → ℕ) (hγ : ∀ i, ratioExp h k i = l → γ i = 0) :
    ∫ u in unitBox d, (∏ i, faceProj h k l u i ^ γ i) *
        (faceLeadConst h k l β * residualWeight h k l u) =
      monomialMixedConst (fun i => h i + γ i) k l β := by
  -- the integrand is a product of one-dimensional factors
  have hpt : ∀ u ∈ unitBox d,
      (∏ i, faceProj h k l u i ^ γ i) * (faceLeadConst h k l β * residualWeight h k l u) =
        faceLeadConst h k l β * ∏ i, (if ratioExp h k i = l then (1 : ℝ)
          else u i ^ ((h i : ℝ) + γ i - 2 * (k i : ℝ) * l)) := by
    intro u hu
    unfold residualWeight faceProj
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [hγ i hi, pow_zero, one_mul]
    · have hu0 : 0 < u i := (hu i (mem_univ i)).1
      rw [← Real.rpow_natCast, ← Real.rpow_add hu0]
      congr 1
      ring
  rw [setIntegral_congr_fun (measurableSet_unitBox d) hpt, integral_const_mul]
  rw [restrict_unitBox, integral_fintype_prod_eq_prod (f := fun i (t : ℝ) =>
    if ratioExp h k i = l then (1 : ℝ) else t ^ ((h i : ℝ) + γ i - 2 * (k i : ℝ) * l))]
  -- evaluate the factors and compare with the mixed constant
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
  unfold monomialMixedConst faceLeadConst
  have hm : multCount (ratioExp (fun i => h i + γ i) k) l = multCount (ratioExp h k) l := by
    unfold multCount
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ratioExp h k i = l
    · rw [if_pos hi, if_pos (by rw [ratioExp_shift_eq_of_zero h k γ i (hγ i hi), hi])]
    · rw [if_neg hi, if_neg]
      intro h'
      exact hi (le_antisymm (h' ▸ ratioExp_le_shift h k γ hk i) (hmin i))
  rw [hm, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : ratioExp h k i = l
  · rw [if_pos hi, if_pos hi, if_pos (by rw [ratioExp_shift_eq_of_zero h k γ i (hγ i hi), hi]),
      mul_one]
  · have hi' : ratioExp (fun i => h i + γ i) k i ≠ l := fun h' =>
      hi (le_antisymm (h' ▸ ratioExp_le_shift h k γ hk i) (hmin i))
    rw [if_neg hi, if_neg hi, if_neg hi', one_mul]
    push_cast
    ring_nf

/-- **Face moments (non-face shifts)**: a monomial involving a minimal coordinate has zero face
moment. -/
theorem face_moment_eq_zero {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) (γ : Fin d → ℕ)
    (hγ : ∃ j, ratioExp h k j = l ∧ γ j ≠ 0) :
    ∫ u in unitBox d, (∏ i, faceProj h k l u i ^ γ i) *
        (faceLeadConst h k l β * residualWeight h k l u) = 0 := by
  obtain ⟨j, hj, hγj⟩ := hγ
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  have : faceProj h k l u j ^ γ j = 0 := by
    simp only [faceProj, if_pos hj]
    exact zero_pow hγj
  change (∏ i, faceProj h k l u i ^ γ i) * (faceLeadConst h k l β * residualWeight h k l u) = 0
  rw [Finset.prod_eq_zero (Finset.mem_univ j) this, zero_mul]

/-- The normalised finite-`N` weight. -/
noncomputable def normWeight {d : ℕ} (h k : Fin d → ℕ) (l β N : ℝ) (x : Fin d → ℝ) : ℝ :=
  (∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))) /
    (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))

theorem normWeight_integrableOn {d : ℕ} (h k : Fin d → ℕ) (l β N : ℝ) :
    IntegrableOn (normWeight h k l β N) (unitBox d) :=
  (monomialBox_integrableOn d h k β N).div_const _

theorem normWeight_nonneg {d : ℕ} (h k : Fin d → ℕ) (l β N : ℝ) (hN : 1 < N) (x : Fin d → ℝ)
    (hx : x ∈ unitBox d) : 0 ≤ normWeight h k l β N x := by
  unfold normWeight
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  exact div_nonneg (monomialBox_integrand_nonneg d h k β N x hx) (by positivity)

/-- The monomial moments of the normalised weight are the shifted normalised moments. -/
theorem integral_monomial_normWeight {d : ℕ} (h k : Fin d → ℕ) (l β N : ℝ) (γ : Fin d → ℕ) :
    ∫ x in unitBox d, (∏ i, x i ^ γ i) * normWeight h k l β N x =
      monomialBoxReal d (fun i => h i + γ i) k β N /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
  unfold normWeight monomialBoxReal
  rw [← integral_div]
  refine setIntegral_congr_fun (measurableSet_unitBox d) fun x _ => ?_
  simp only [pow_add, Finset.prod_mul_distrib]
  ring

/-- **Continuous-amplitude asymptotic**: for a continuous amplitude `η`,
`I_η(N) / (N^{-λ} (log N)^{|J|-1}) →
  Γ(λ)β^{-λ}/(|J|-1)! ∏_{J} 1/(2kⱼ) ∫ η(P_J u) ∏_{∉J} uᵢ^{hᵢ-2kᵢλ} du`. -/
theorem amplitude_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (η : (Fin (d + 1) → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => (∫ x in unitBox (d + 1),
        η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (amplitudeCoeff h k l β η)) := by
  have hT := tendsto_integral_of_monomials (d + 1) (unitBox (d + 1)) (measurableSet_unitBox _)
    (fun _ => id) (faceProj h k l) (fun _ => fun x hx => unitBox_subset_closedCube _ hx)
    (faceProj_mapsTo h k l) (fun _ => measurable_id) (measurable_faceProj h k l)
    (fun N => normWeight h k l β N) (fun u => faceLeadConst h k l β * residualWeight h k l u)
    (fun N => normWeight_integrableOn h k l β N)
    ((residualWeight_integrableOn h k hk l hmin).const_mul _)
    (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      exact fun x hx => normWeight_nonneg h k l β N hN x hx)
    (fun u hu => mul_nonneg (faceLeadConst_pos h k hk l β hl hβ).le
      (residualWeight_nonneg h k l u hu))
    (fun γ => ?_) η hη
  · unfold amplitudeCoeff
    rw [← integral_const_mul]
    have hlim : ∫ x in unitBox (d + 1), η (faceProj h k l x) *
        (faceLeadConst h k l β * residualWeight h k l x) =
        ∫ x in unitBox (d + 1), faceLeadConst h k l β * (η (faceProj h k l x) * residualWeight h k l x) :=
      setIntegral_congr_fun (measurableSet_unitBox _) fun x _ => by ring
    rw [hlim] at hT
    refine hT.congr' (Eventually.of_forall fun N => ?_)
    simp only [id]
    rw [← integral_div]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun x _ => ?_
    unfold normWeight
    ring
  · -- monomial moments
    simp only [id]
    have hrw : (fun N => ∫ x in unitBox (d + 1), (∏ i, x i ^ γ i) * normWeight h k l β N x) =
        fun N => monomialBoxReal (d + 1) (fun i => h i + γ i) k β N /
          (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) :=
      funext fun N => integral_monomial_normWeight h k l β N γ
    rw [hrw]
    by_cases hγ : ∀ i, ratioExp h k i = l → γ i = 0
    · rw [face_moment_eq h k hk l β hmin γ hγ]
      exact shiftedMoment_tendsto_of_face d h k hk l β hl hβ hmin hatt γ hγ
    · push Not at hγ
      obtain ⟨j, hj, hγj⟩ := hγ
      rw [face_moment_eq_zero h k l β γ ⟨j, hj, hγj⟩]
      exact shiftedMoment_tendsto_zero d h k hk l β hl hβ hmin hatt γ ⟨j, hj, hγj⟩

end Laplace.Grammar
