/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.RadialCurvature

/-!
# The angular lower bound: thermodynamic length dominates ambient Fisher–Rao distance

For a non-degenerate state density and `0 < s ≤ t`,

  `2 arccos ρ(s,t) ≤ ∫_s^t √Var_u(ℓ) du`   (`two_arccos_affinity_le_lawLength`),

where `ρ(s,t) = Z((s+t)/2)/√(Z(s)Z(t))` is the Bhattacharyya affinity: the length of the featureless
line between two temperatures dominates the ambient Fisher–Rao distance `2 arccos ρ` of its
endpoints on the `L²` sphere. The proof is the sphere argument made elementary: with `m = (s+u)/2`,

  `ρ'(u) = (ρ/2)(⟨ℓ⟩_u − ⟨ℓ⟩_m)`   (`hasDerivAt_affinityExp`),

and Cauchy–Schwarz for the pair `(ℓ − ⟨ℓ⟩_u) e^{-uℓ/2}`, `e^{-sℓ/2} − (Z(m)/Z(u)) e^{-uℓ/2}` gives

  `ρ² (⟨ℓ⟩_m − ⟨ℓ⟩_u)² ≤ (1 − ρ²) Var_u(ℓ)`   (`affinity_cauchy_schwarz`),

so `θ = arccos ∘ ρ` satisfies `θ' ≤ ½ √Var_u`; integrating from `θ(s) = 0` gives the bound. Combined
with `tendsto_fisherRao_pi`, this is Astra's length–distance theorem: the endpoints approach the
maximal separation `π` while the path length diverges like `√λ log t`.
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace Laplace.Multi

/-- Cauchy–Schwarz for integrals, by the discriminant: `(∫ fg)² ≤ (∫ f²)(∫ g²)`. -/
theorem integral_mul_sq_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x ↦ f x * f x) ν) (hg : Integrable (fun x ↦ g x * g x) ν)
    (hfg : Integrable (fun x ↦ f x * g x) ν) :
    (∫ x, f x * g x ∂ν) ^ 2 ≤ (∫ x, f x * f x ∂ν) * ∫ x, g x * g x ∂ν := by
  have key : ∀ l : ℝ, 0 ≤ (∫ x, g x * g x ∂ν) * (l * l) + (-2 * ∫ x, f x * g x ∂ν) * l +
      ∫ x, f x * f x ∂ν := fun l ↦ by
    have e : ∀ x, (f x - l * g x) * (f x - l * g x) =
        (g x * g x) * (l * l) - (2 * l) * (f x * g x) + f x * f x := fun x ↦ by ring
    have hnn : 0 ≤ ∫ x, (f x - l * g x) * (f x - l * g x) ∂ν :=
      integral_nonneg fun x ↦ mul_self_nonneg _
    simp_rw [e] at hnn
    have I1 : Integrable (fun x ↦ (g x * g x) * (l * l)) ν := hg.mul_const _
    have I2 : Integrable (fun x ↦ (2 * l) * (f x * g x)) ν := hfg.const_mul _
    have I12 : Integrable (fun x ↦ (g x * g x) * (l * l) - (2 * l) * (f x * g x)) ν := I1.sub I2
    rw [integral_add I12 hf, integral_sub I1 I2, MeasureTheory.integral_mul_const,
      MeasureTheory.integral_const_mul] at hnn
    linarith
  have := discrim_le_zero key
  rw [discrim] at this
  nlinarith

/-- The affinity in exponential form, `ρ(s,u) = exp(F((s+u)/2) − (F(s) + F(u))/2)`. -/
noncomputable def affinityExp (ν : Measure ℝ) (s u : ℝ) : ℝ :=
  Real.exp (Real.log (lawMoment ν 0 ((s + u) / 2)) -
    (Real.log (lawMoment ν 0 s) + Real.log (lawMoment ν 0 u)) / 2)

theorem affinityExp_eq (ν : Measure ℝ) {s u : ℝ} (hs : 0 < lawMoment ν 0 s)
    (hu : 0 < lawMoment ν 0 u) (hm : 0 < lawMoment ν 0 ((s + u) / 2)) :
    affinityExp ν s u = lawAffinity ν s u := by
  unfold affinityExp
  rw [← log_lawAffinity ν hs hu hm, Real.exp_log]
  unfold lawAffinity
  exact div_pos hm (Real.sqrt_pos.mpr (mul_pos hs hu))

theorem affinityExp_pos (ν : Measure ℝ) (s u : ℝ) : 0 < affinityExp ν s u := Real.exp_pos _

theorem affinityExp_self (ν : Measure ℝ) (s : ℝ) : affinityExp ν s s = 1 := by
  unfold affinityExp
  rw [show (s + s) / 2 = s by ring]
  rw [show Real.log (lawMoment ν 0 s) - (Real.log (lawMoment ν 0 s) +
    Real.log (lawMoment ν 0 s)) / 2 = 0 by ring, Real.exp_zero]

/-- `ρ(s,u) < 1` for `s < u` (strict log-convexity of `Z` for a non-degenerate state density). -/
theorem affinityExp_lt_one (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν) (hK : 3 ≤ K)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) (hnd : ∀ u > 0, 0 < lawVar ν u) {s u : ℝ} (hs : 0 < s)
    (hsu : s < u) : affinityExp ν s u < 1 := by
  unfold affinityExp
  rw [← Real.exp_zero, Real.exp_lt_exp]
  have h := bhattacharyya_eq_integral_var ν hpos hint hK hZ hs hsu.le
  set m := (s + u) / 2 with hm
  have hsm : s < m := by rw [hm]; linarith
  have hmu : m < u := by rw [hm]; linarith
  have hVc := continuousOn_lawVar ν hpos hint hK hZ
  have h1 : 0 < ∫ v in s..m, (v - s) * lawVar ν v := by
    refine intervalIntegral_pos_of_pos_on ?_ (fun v hv ↦ ?_) hsm
    · refine (ContinuousOn.mul (continuousOn_id.sub continuousOn_const)
        (hVc.mono ?_)).intervalIntegrable
      rw [uIcc_of_le hsm.le]
      exact fun v hv ↦ lt_of_lt_of_le hs hv.1
    · exact mul_pos (by linarith [hv.1]) (hnd v (by linarith [hv.1]))
  have h2 : 0 < ∫ v in m..u, (u - v) * lawVar ν v := by
    refine intervalIntegral_pos_of_pos_on ?_ (fun v hv ↦ ?_) hmu
    · refine (ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
        (hVc.mono ?_)).intervalIntegrable
      rw [uIcc_of_le hmu.le]
      exact fun v hv ↦ lt_of_lt_of_le (by linarith) hv.1
    · exact mul_pos (by linarith [hv.2]) (hnd v (by linarith [hv.1]))
  linarith

/-- **The derivative of the affinity**: `ρ'(u) = (ρ/2)(⟨ℓ⟩_u − ⟨ℓ⟩_m)`, `m = (s+u)/2`. -/
theorem hasDerivAt_affinityExp (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν) (hK : 1 ≤ K)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    HasDerivAt (fun v ↦ affinityExp ν s v)
      (affinityExp ν s u / 2 * (lawMoment ν 1 u / lawMoment ν 0 u -
        lawMoment ν 1 ((s + u) / 2) / lawMoment ν 0 ((s + u) / 2))) u := by
  have hm : 0 < (s + u) / 2 := by positivity
  have hFm := hasDerivAt_lawLogZ ν hpos hint hK hm (hZ _ hm)
  have hFu := hasDerivAt_lawLogZ ν hpos hint hK hu (hZ _ hu)
  have haff : HasDerivAt (fun v : ℝ ↦ (s + v) / 2) (1 / 2) u := by
    have := ((hasDerivAt_id u).const_add s).div_const 2
    simpa using this
  have hcomp := hFm.comp u haff
  have hinner := hcomp.sub
    ((hasDerivAt_const u (Real.log (lawMoment ν 0 s))).add hFu |>.div_const 2)
  have := hinner.exp
  refine this.congr_deriv ?_
  unfold affinityExp
  simp only [Function.comp_apply, Pi.sub_apply, Pi.add_apply]
  ring

/-- **Cauchy–Schwarz between the midpoint and the endpoint** (moment form): with `m = (s+u)/2`,
`Z(m)² (⟨ℓ⟩_m − ⟨ℓ⟩_u)² ≤ Z(u) Var_u · (Z(s) − Z(m)²/Z(u))`. -/
theorem affinity_cauchy_schwarz (ν : Measure ℝ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν) (hK : 2 ≤ K)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    (lawMoment ν 0 ((s + u) / 2) * (lawMoment ν 1 ((s + u) / 2) / lawMoment ν 0 ((s + u) / 2) -
        lawMoment ν 1 u / lawMoment ν 0 u)) ^ 2 ≤
      (lawMoment ν 0 u * lawVar ν u) *
        (lawMoment ν 0 s - lawMoment ν 0 ((s + u) / 2) ^ 2 / lawMoment ν 0 u) := by
  set m := (s + u) / 2 with hm
  have hm0 : 0 < m := by positivity
  set a := lawMoment ν 1 u / lawMoment ν 0 u with ha
  set c := lawMoment ν 0 m / lawMoment ν 0 u with hc
  -- the two functions
  set f : ℝ → ℝ := fun ℓ ↦ (ℓ - a) * Real.exp (-(u / 2 * ℓ)) with hf
  set g : ℝ → ℝ := fun ℓ ↦ Real.exp (-(s / 2 * ℓ)) - c * Real.exp (-(u / 2 * ℓ)) with hg
  have euu : ∀ ℓ, Real.exp (-(u / 2 * ℓ)) * Real.exp (-(u / 2 * ℓ)) = Real.exp (-(u * ℓ)) :=
    fun ℓ ↦ by rw [← Real.exp_add]; congr 1; ring
  have ess : ∀ ℓ, Real.exp (-(s / 2 * ℓ)) * Real.exp (-(s / 2 * ℓ)) = Real.exp (-(s * ℓ)) :=
    fun ℓ ↦ by rw [← Real.exp_add]; congr 1; ring
  have esu : ∀ ℓ, Real.exp (-(s / 2 * ℓ)) * Real.exp (-(u / 2 * ℓ)) = Real.exp (-(m * ℓ)) :=
    fun ℓ ↦ by rw [← Real.exp_add]; congr 1; rw [hm]; ring
  -- integrability
  have I : ∀ v > 0, ∀ k ≤ 2, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν :=
    fun v hv k hk ↦ hint v hv k (by omega)
  have hZu := hZ u hu
  have hZm := hZ m hm0
  -- `f · f`
  have ef : ∀ ℓ, f ℓ * f ℓ = ℓ ^ 2 * Real.exp (-(u * ℓ)) - (2 * a) * (ℓ ^ 1 * Real.exp (-(u * ℓ)))
      + a ^ 2 * (ℓ ^ 0 * Real.exp (-(u * ℓ))) := fun ℓ ↦ by
    simp only [hf]
    rw [show (ℓ - a) * Real.exp (-(u / 2 * ℓ)) * ((ℓ - a) * Real.exp (-(u / 2 * ℓ))) =
      (ℓ - a) ^ 2 * (Real.exp (-(u / 2 * ℓ)) * Real.exp (-(u / 2 * ℓ))) by ring, euu]
    ring
  have J2 : Integrable (fun ℓ ↦ ℓ ^ 2 * Real.exp (-(u * ℓ))) ν := I u hu 2 le_rfl
  have J1 : Integrable (fun ℓ ↦ (2 * a) * (ℓ ^ 1 * Real.exp (-(u * ℓ)))) ν :=
    (I u hu 1 (by norm_num)).const_mul _
  have J0 : Integrable (fun ℓ ↦ a ^ 2 * (ℓ ^ 0 * Real.exp (-(u * ℓ)))) ν :=
    (I u hu 0 (by norm_num)).const_mul _
  have J21 : Integrable (fun ℓ ↦ ℓ ^ 2 * Real.exp (-(u * ℓ)) -
      (2 * a) * (ℓ ^ 1 * Real.exp (-(u * ℓ)))) ν := J2.sub J1
  have Iff : Integrable (fun ℓ ↦ f ℓ * f ℓ) ν := by
    simp_rw [ef]
    exact J21.add J0
  have vff : (∫ ℓ, f ℓ * f ℓ ∂ν) = lawMoment ν 0 u * lawVar ν u := by
    simp_rw [ef]
    rw [integral_add J21 J0, integral_sub J2 J1, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    unfold lawVar lawExp
    have e2 : (∫ ℓ, ℓ * ℓ * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 2 u :=
      integral_congr_ae (Filter.Eventually.of_forall fun ℓ ↦ by ring)
    have e1 : (∫ ℓ, ℓ * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 1 u := by simp [lawMoment]
    have e0 : (∫ ℓ, Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 0 u := by simp [lawMoment]
    have r2 : (∫ ℓ, ℓ ^ 2 * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 2 u := rfl
    have r1 : (∫ ℓ, ℓ ^ 1 * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 1 u := rfl
    have r0 : (∫ ℓ, ℓ ^ 0 * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 0 u := rfl
    rw [e2, e1, e0, r2, r1, r0, ha]
    field_simp
    ring
  -- `g · g`
  have eg : ∀ ℓ, g ℓ * g ℓ = ℓ ^ 0 * Real.exp (-(s * ℓ)) - (2 * c) * (ℓ ^ 0 * Real.exp (-(m * ℓ)))
      + c ^ 2 * (ℓ ^ 0 * Real.exp (-(u * ℓ))) := fun ℓ ↦ by
    simp only [hg]
    rw [show (Real.exp (-(s / 2 * ℓ)) - c * Real.exp (-(u / 2 * ℓ))) *
      (Real.exp (-(s / 2 * ℓ)) - c * Real.exp (-(u / 2 * ℓ))) =
      Real.exp (-(s / 2 * ℓ)) * Real.exp (-(s / 2 * ℓ)) -
        2 * c * (Real.exp (-(s / 2 * ℓ)) * Real.exp (-(u / 2 * ℓ))) +
        c ^ 2 * (Real.exp (-(u / 2 * ℓ)) * Real.exp (-(u / 2 * ℓ))) by ring, ess, esu, euu]
    ring
  have G2 : Integrable (fun ℓ ↦ ℓ ^ 0 * Real.exp (-(s * ℓ))) ν := I s hs 0 (by norm_num)
  have G1 : Integrable (fun ℓ ↦ (2 * c) * (ℓ ^ 0 * Real.exp (-(m * ℓ)))) ν :=
    (I m hm0 0 (by norm_num)).const_mul _
  have G0 : Integrable (fun ℓ ↦ c ^ 2 * (ℓ ^ 0 * Real.exp (-(u * ℓ)))) ν :=
    (I u hu 0 (by norm_num)).const_mul _
  have G21 : Integrable (fun ℓ ↦ ℓ ^ 0 * Real.exp (-(s * ℓ)) -
      (2 * c) * (ℓ ^ 0 * Real.exp (-(m * ℓ)))) ν := G2.sub G1
  have Igg : Integrable (fun ℓ ↦ g ℓ * g ℓ) ν := by
    simp_rw [eg]
    exact G21.add G0
  have vgg : (∫ ℓ, g ℓ * g ℓ ∂ν) = lawMoment ν 0 s - lawMoment ν 0 m ^ 2 / lawMoment ν 0 u := by
    simp_rw [eg]
    rw [integral_add G21 G0, integral_sub G2 G1, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    have rs : (∫ ℓ, ℓ ^ 0 * Real.exp (-(s * ℓ)) ∂ν) = lawMoment ν 0 s := rfl
    have rm : (∫ ℓ, ℓ ^ 0 * Real.exp (-(m * ℓ)) ∂ν) = lawMoment ν 0 m := rfl
    have ru : (∫ ℓ, ℓ ^ 0 * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 0 u := rfl
    rw [rs, rm, ru, hc]
    field_simp
    ring
  -- `f · g`
  have efg : ∀ ℓ, f ℓ * g ℓ = (ℓ ^ 1 * Real.exp (-(m * ℓ)) - a * (ℓ ^ 0 * Real.exp (-(m * ℓ))))
      - c * (ℓ ^ 1 * Real.exp (-(u * ℓ)) - a * (ℓ ^ 0 * Real.exp (-(u * ℓ)))) := fun ℓ ↦ by
    simp only [hf, hg]
    rw [show (ℓ - a) * Real.exp (-(u / 2 * ℓ)) *
      (Real.exp (-(s / 2 * ℓ)) - c * Real.exp (-(u / 2 * ℓ))) =
      (ℓ - a) * (Real.exp (-(s / 2 * ℓ)) * Real.exp (-(u / 2 * ℓ))) -
        c * ((ℓ - a) * (Real.exp (-(u / 2 * ℓ)) * Real.exp (-(u / 2 * ℓ)))) by ring, esu, euu]
    ring
  have H1m : Integrable (fun ℓ ↦ ℓ ^ 1 * Real.exp (-(m * ℓ))) ν := I m hm0 1 (by norm_num)
  have H0m : Integrable (fun ℓ ↦ a * (ℓ ^ 0 * Real.exp (-(m * ℓ)))) ν :=
    (I m hm0 0 (by norm_num)).const_mul _
  have Hm : Integrable
      (fun ℓ ↦ ℓ ^ 1 * Real.exp (-(m * ℓ)) - a * (ℓ ^ 0 * Real.exp (-(m * ℓ)))) ν :=
    H1m.sub H0m
  have H1u : Integrable (fun ℓ ↦ ℓ ^ 1 * Real.exp (-(u * ℓ))) ν := I u hu 1 (by norm_num)
  have H0u : Integrable (fun ℓ ↦ a * (ℓ ^ 0 * Real.exp (-(u * ℓ)))) ν :=
    (I u hu 0 (by norm_num)).const_mul _
  have Hu : Integrable
      (fun ℓ ↦ ℓ ^ 1 * Real.exp (-(u * ℓ)) - a * (ℓ ^ 0 * Real.exp (-(u * ℓ)))) ν :=
    H1u.sub H0u
  have Hu' : Integrable (fun ℓ ↦ c * (ℓ ^ 1 * Real.exp (-(u * ℓ)) -
      a * (ℓ ^ 0 * Real.exp (-(u * ℓ))))) ν := Hu.const_mul _
  have Ifg : Integrable (fun ℓ ↦ f ℓ * g ℓ) ν := by
    simp_rw [efg]
    exact Hm.sub Hu'
  have vfg : (∫ ℓ, f ℓ * g ℓ ∂ν) = lawMoment ν 0 m *
      (lawMoment ν 1 m / lawMoment ν 0 m - lawMoment ν 1 u / lawMoment ν 0 u) := by
    simp_rw [efg]
    rw [integral_sub Hm Hu', integral_sub H1m H0m, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, integral_sub H1u H0u, MeasureTheory.integral_const_mul]
    have r1m : (∫ ℓ, ℓ ^ 1 * Real.exp (-(m * ℓ)) ∂ν) = lawMoment ν 1 m := rfl
    have r0m : (∫ ℓ, ℓ ^ 0 * Real.exp (-(m * ℓ)) ∂ν) = lawMoment ν 0 m := rfl
    have r1u : (∫ ℓ, ℓ ^ 1 * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 1 u := rfl
    have r0u : (∫ ℓ, ℓ ^ 0 * Real.exp (-(u * ℓ)) ∂ν) = lawMoment ν 0 u := rfl
    rw [r1m, r0m, r1u, r0u, ha, hc]
    field_simp
    ring
  have key := integral_mul_sq_le Iff Igg Ifg
  rw [vff, vgg, vfg] at key
  exact key


/-- `ρ(s,u)² = Z(m)²/(Z(s) Z(u))`. -/
theorem affinityExp_sq (ν : Measure ℝ) {s u : ℝ} (hs : 0 < lawMoment ν 0 s)
    (hu : 0 < lawMoment ν 0 u) (hm : 0 < lawMoment ν 0 ((s + u) / 2)) :
    affinityExp ν s u ^ 2 =
      lawMoment ν 0 ((s + u) / 2) ^ 2 / (lawMoment ν 0 s * lawMoment ν 0 u) := by
  rw [affinityExp_eq ν hs hu hm]
  unfold lawAffinity
  rw [div_pow, Real.sq_sqrt (mul_pos hs hu).le]

/-- **The derivative of `θ = arccos ∘ ρ` is at most half the radial speed**: for `s < u`,
`θ'(u) ≤ ½ √Var_u(ℓ)`. -/
theorem hasDerivAt_arccos_affinityExp (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν) (hK : 3 ≤ K)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) (hnd : ∀ u > 0, 0 < lawVar ν u) {s u : ℝ} (hs : 0 < s)
    (hsu : s < u) :
    ∃ d, HasDerivAt (fun v ↦ Real.arccos (affinityExp ν s v)) d u ∧
      d ≤ Real.sqrt (lawVar ν u) / 2 := by
  have hu : 0 < u := lt_trans hs hsu
  have hm0 : 0 < (s + u) / 2 := by positivity
  have hρ1 := affinityExp_lt_one ν hpos hint hK hZ hnd hs hsu
  have hρ0 := affinityExp_pos ν s u
  have hρ := hasDerivAt_affinityExp ν hpos hint (by omega) hZ hs hu
  have harc := (Real.hasDerivAt_arccos (by linarith) hρ1.ne).comp u hρ
  refine ⟨_, harc, ?_⟩
  -- the bound via Cauchy–Schwarz
  set ρ := affinityExp ν s u with hρdef
  set a := lawMoment ν 1 u / lawMoment ν 0 u with ha
  set b := lawMoment ν 1 ((s + u) / 2) / lawMoment ν 0 ((s + u) / 2) with hb
  have hcs := affinity_cauchy_schwarz ν hint (by omega) hZ hs hu
  have hZs := hZ s hs
  have hZu := hZ u hu
  have hZm := hZ _ hm0
  have hρsq : ρ ^ 2 = lawMoment ν 0 ((s + u) / 2) ^ 2 / (lawMoment ν 0 s * lawMoment ν 0 u) :=
    affinityExp_sq ν hZs hZu hZm
  have h1ρ : 0 < 1 - ρ ^ 2 := by nlinarith
  -- `ρ² (b − a)² ≤ (1 − ρ²) Var_u`
  have hkey : ρ ^ 2 * (b - a) ^ 2 ≤ (1 - ρ ^ 2) * lawVar ν u := by
    rw [hρsq]
    rw [← hb, ← ha] at hcs
    have e1 : lawMoment ν 0 ((s + u) / 2) ^ 2 / (lawMoment ν 0 s * lawMoment ν 0 u) * (b - a) ^ 2 =
        (lawMoment ν 0 ((s + u) / 2) * (b - a)) ^ 2 / (lawMoment ν 0 s * lawMoment ν 0 u) := by
      ring
    have e2 : (1 - lawMoment ν 0 ((s + u) / 2) ^ 2 / (lawMoment ν 0 s * lawMoment ν 0 u)) *
        lawVar ν u = (lawMoment ν 0 u * lawVar ν u) *
          (lawMoment ν 0 s - lawMoment ν 0 ((s + u) / 2) ^ 2 / lawMoment ν 0 u) /
          (lawMoment ν 0 s * lawMoment ν 0 u) := by
      field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hcs (by positivity)
  -- take square roots
  have hsq : ρ * (b - a) ≤ Real.sqrt (1 - ρ ^ 2) * Real.sqrt (lawVar ν u) := by
    calc ρ * (b - a) ≤ |ρ * (b - a)| := le_abs_self _
      _ = Real.sqrt ((ρ * (b - a)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((1 - ρ ^ 2) * lawVar ν u) := by
          refine Real.sqrt_le_sqrt ?_
          rw [mul_pow]
          exact hkey
      _ = Real.sqrt (1 - ρ ^ 2) * Real.sqrt (lawVar ν u) := Real.sqrt_mul h1ρ.le _
  -- the derivative value
  have hs1 : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos.mpr h1ρ
  change -(1 / Real.sqrt (1 - ρ ^ 2)) * (ρ / 2 * (a - b)) ≤ Real.sqrt (lawVar ν u) / 2
  rw [show -(1 / Real.sqrt (1 - ρ ^ 2)) * (ρ / 2 * (a - b)) =
    (ρ * (b - a)) / (2 * Real.sqrt (1 - ρ ^ 2)) by field_simp; ring,
    div_le_div_iff₀ (by positivity) two_pos]
  nlinarith [hsq, hs1]

/-- **The angular lower bound**: for a non-degenerate state density and `0 < s ≤ t`,
`2 arccos ρ(s,t) ≤ ∫_s^t √Var_u(ℓ) du`. -/
theorem two_arccos_affinityExp_le (ν : Measure ℝ) (hpos : ∀ᵐ ℓ ∂ν, 0 ≤ ℓ) {K : ℕ}
    (hint : ∀ v > 0, ∀ k ≤ K, Integrable (fun ℓ ↦ ℓ ^ k * Real.exp (-(v * ℓ))) ν) (hK : 3 ≤ K)
    (hZ : ∀ u > 0, 0 < lawMoment ν 0 u) (hnd : ∀ u > 0, 0 < lawVar ν u) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) :
    2 * Real.arccos (affinityExp ν s t) ≤ ∫ u in s..t, Real.sqrt (lawVar ν u) := by
  -- the speed is continuous on `(0, ∞)`
  have hVc : ContinuousOn (fun u ↦ Real.sqrt (lawVar ν u)) (Ioi 0) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_lawVar ν hpos hint hK hZ)
  have hsub : Icc s t ⊆ Ioi 0 := fun u hu ↦ lt_of_lt_of_le hs hu.1
  -- the affinity is continuous on `(0, ∞)`
  have hρc : ContinuousOn (fun v ↦ affinityExp ν s v) (Ioi 0) := fun u hu ↦
    (hasDerivAt_affinityExp ν hpos hint (by omega) hZ hs hu).continuousAt.continuousWithinAt
  -- the comparison function
  set Φ : ℝ → ℝ := fun v ↦ (∫ u in s..v, Real.sqrt (lawVar ν u)) / 2 -
    Real.arccos (affinityExp ν s v) with hΦ
  have hΦc : ContinuousOn Φ (Icc s t) := by
    refine ContinuousOn.sub (ContinuousOn.div_const ?_ _)
      (Real.continuous_arccos.comp_continuousOn (hρc.mono hsub))
    have := continuousOn_primitive_interval (a := s) (b := t) (μ := volume)
      (f := fun u ↦ Real.sqrt (lawVar ν u))
      ((hVc.mono (by rw [uIcc_of_le hst]; exact hsub)).integrableOn_compact isCompact_uIcc)
    rwa [uIcc_of_le hst] at this
  have hΦd : ∀ v ∈ Ioo s t, ∃ d, HasDerivAt Φ d v ∧ 0 ≤ d := fun v hv ↦ by
    have hv0 : 0 < v := lt_trans hs hv.1
    obtain ⟨d, hd, hdle⟩ := hasDerivAt_arccos_affinityExp ν hpos hint hK hZ hnd hs hv.1
    have hD : HasDerivAt (fun v ↦ ∫ u in s..v, Real.sqrt (lawVar ν u))
        (Real.sqrt (lawVar ν v)) v := by
      refine integral_hasDerivAt_right ?_ ?_ (hVc.continuousAt (Ioi_mem_nhds hv0))
      · refine (hVc.mono ?_).intervalIntegrable
        rw [uIcc_of_le hv.1.le]
        exact fun u hu ↦ lt_of_lt_of_le hs hu.1
      · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hVc v hv0
    refine ⟨Real.sqrt (lawVar ν v) / 2 - d, (hD.div_const 2).sub hd, by linarith⟩
  have hmono : MonotoneOn Φ (Icc s t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc s t) hΦc ?_ ?_
    · rw [interior_Icc]
      intro v hv
      obtain ⟨d, hd, _⟩ := hΦd v hv
      exact hd.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro v hv
      obtain ⟨d, hd, hd0⟩ := hΦd v hv
      rw [hd.deriv]
      exact hd0
  have h0 := hmono (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst) hst
  simp only [hΦ, integral_same, zero_div, affinityExp_self, Real.arccos_one, sub_zero] at h0
  linarith

end Laplace.Multi
