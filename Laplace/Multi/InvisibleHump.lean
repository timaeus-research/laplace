/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ReconstructionBias
import Laplace.Multi.MixtureBridge
import Laplace.Multi.BridgeResidual
import Laplace.Multi.FiniteResponse
import Laplace.Multi.FixedNormalLimit
import Laplace.Multi.AtlasRefinement

/-!
# The invisible information along the affine data path is not monotone

Along the affine data path `D_t = (1 − t) ν + t D` the total information splits as
`KL(D_t ‖ ν) = 𝓘(M_t) + R(t)` with `R(t) = KL(D_t ‖ Π(M_t))` the invisible part
(`atlas_decomposition_mixture`). One might hope that `R` decreases toward the featureless end. It
does not: on three points with the uniform reference law, the single feature `S(x) = x` and the
family member `D ∝ e^x`, both endpoints are in the family (`R(0) = R(1) = 0`) while every interior
mixture leaves it (`R(t) > 0`): a mixture of two exponential-family members violates the
log-linear identity `p₀ p₂ = p₁²` (`humpResidual_pos`). Hence the invisible information is neither
antitone nor monotone along the path (`humpResidual_not_antitone`). What survives are the envelopes
`R(s) ≤ s KL(D ‖ ν) − 𝓘(M_s)` and `R(s) ≤ s R(1) + s 𝓘(M) − 𝓘(M_s)`
(`invisibleInformation_bridge_le_total`, `invisibleInformation_bridge_le`).
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace Laplace.Multi

section Envelopes

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J] (ν D : Measure X)
  [IsProbabilityMeasure ν] [IsProbabilityMeasure D] (S : J → X → ℝ) (hD : D ≪ ν)
  {a b : ℝ≥0} (hab : a + b = 1) (hfin : klDiv D ν ≠ ⊤)
include hD hab hfin

/-- **The total envelope of the invisible information**: `R_s ≤ b KL(D ‖ ν) − 𝓘(M_s)`. -/
theorem invisibleInformation_bridge_le_total :
    (klDiv (a • ν + b • D) ν).toReal -
        (genRate ν S (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))).toReal ≤
      (b : ℝ) * (klDiv D ν).toReal -
        (genRate ν S (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))).toReal := by
  have hup : (klDiv (a • ν + b • D) ν).toReal ≤ (b : ℝ) * (klDiv D ν).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)
      (klDiv_mixture_self_le ν D hD hab)
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
  linarith

/-- **The sharper envelope**: `R_s ≤ b R₁ + b 𝓘(M) − 𝓘(M_s)`, so the invisible information at
`s` is controlled by the endpoint invisible information and the visible-information gap. -/
theorem invisibleInformation_bridge_le (ha : 0 < a) (hb : 0 < b) :
    (klDiv (a • ν + b • D) ν).toReal -
        (genRate ν S (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))).toReal ≤
      (b : ℝ) * ((klDiv D ν).toReal - (genRate ν S (fun i ↦ ∫ x, S i x ∂D)).toReal) +
        (b : ℝ) * (genRate ν S (fun i ↦ ∫ x, S i x ∂D)).toReal -
        (genRate ν S (fun i ↦ ∫ x, S i x ∂(a • ν + b • D))).toReal := by
  have h := (invisibleInformation_bridge_modulus ν D S hD hab ha hb hfin).1
  have hab' : (a : ℝ) + b = 1 := by exact_mod_cast hab
  have hAH : (a : ℝ) * (klDiv D ν).toReal =
      (klDiv D ν).toReal - (b : ℝ) * (klDiv D ν).toReal := by
    rw [show (a : ℝ) = 1 - b by linarith]
    ring
  linarith

end Envelopes

section ThreePoint

/-- The uniform reference law on three points. -/
noncomputable def uniform3 : Measure (Fin 3) := (3 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure uniform3 := ⟨by
  rw [uniform3, Measure.smul_apply, ← Finset.coe_univ, Measure.count_apply_finset,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

/-- The single feature `S(x) = x`. -/
def coordFeature : Fin 1 → Fin 3 → ℝ := fun _ x ↦ (x.val : ℝ)

theorem bdd_coordFeature : ∀ j, Bdd (coordFeature j) := fun _ ↦
  ⟨measurable_of_finite _, 2, fun x ↦ by
    rw [coordFeature, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.le_of_lt_succ x.isLt⟩

/-- The uniform law gives mass `1/3` to every point. -/
theorem uniform3_real_singleton (x : Fin 3) : uniform3.real {x} = 1 / 3 := by
  rw [measureReal_def, uniform3, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]
  norm_num

/-- Point masses of a tilted uniform law. -/
theorem tilted_uniform3_real_singleton (f : Fin 3 → ℝ) (x : Fin 3) :
    (uniform3.tilted f).real {x} =
      1 / 3 * (Real.exp (f x) / ∫ y, Real.exp (f y) ∂uniform3) := by
  have hZ : 0 < ∫ y, Real.exp (f y) ∂uniform3 := integral_exp_pos Integrable.of_finite
  rw [measureReal_def, tilted_apply_eq_ofReal_integral' f (measurableSet_singleton x),
    integral_singleton, uniform3_real_singleton, smul_eq_mul,
    ENNReal.toReal_ofReal (by positivity)]

/-- The family on three points. -/
local notation "Pfam3" => familyMeasure uniform3 (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) coordFeature 1

/-- Point masses of family members are log-linear in the feature. -/
theorem family3_real_singleton (θ : Fin 1 → ℝ) (x : Fin 3) :
    (Pfam3 θ).real {x} =
      (1 / 3 / ∫ y, Real.exp (-1 * dirLoss coordFeature θ y) ∂uniform3) *
        Real.exp (-θ 0 * (x.val : ℝ)) := by
  rw [familyMeasure_one_zero_eq_tilted bdd_coordFeature uniform3 θ, tilted_uniform3_real_singleton]
  simp only [dirLoss, coordFeature, Fin.sum_univ_one]
  ring_nf

/-- Log-linear point masses satisfy `p 0 * p 2 = p 1 * p 1`. -/
theorem loglinear_mul (p : Fin 3 → ℝ) (c k : ℝ) (hp : ∀ x, p x = c * Real.exp (k * (x.val : ℝ))) :
    p 0 * p 2 = p 1 * p 1 := by
  rw [hp 0, hp 1, hp 2]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    mul_zero, Real.exp_zero, mul_one]
  rw [show k * 2 = k + k by ring, Real.exp_add]
  ring

/-- A positive mixture of the uniform law with a log-linear law violates the log-linear identity
in the strict direction `q 0 * q 2 > q 1 * q 1`, whenever the tilt is nonzero. -/
theorem hump_mul (q : Fin 3 → ℝ) (u v k : ℝ) (hu : 0 < u) (hv : 0 < v) (hk : k ≠ 0)
    (hq : ∀ x, q x = u + v * Real.exp (k * (x.val : ℝ))) : q 1 * q 1 < q 0 * q 2 := by
  rw [hq 0, hq 1, hq 2]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    mul_zero, Real.exp_zero, mul_one]
  rw [show k * 2 = k + k by ring, Real.exp_add]
  have hE : Real.exp k ≠ 1 := fun h ↦ hk (Real.exp_eq_one_iff k |>.1 h)
  have hpos : 0 < (Real.exp k - 1) ^ 2 := by
    have : Real.exp k - 1 ≠ 0 := sub_ne_zero.2 hE
    positivity
  nlinarith [mul_pos hu hv]

/-- The data law `D ∝ e^x`, a member of the family. -/
noncomputable def hump3D : Measure (Fin 3) := Pfam3 (fun _ ↦ (-1 : ℝ))

instance : IsProbabilityMeasure hump3D :=
  isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos uniform3) measurable_const (M₀ := 0) (fun _ ↦ by simp) bdd_coordFeature
    (t := 1) _

theorem hump3D_absolutelyContinuous : hump3D ≪ uniform3 := by
  rw [hump3D, familyMeasure_one_zero_eq_tilted bdd_coordFeature uniform3]
  exact tilted_absolutelyContinuous _ _

/-- The affine data path from the uniform law to `D`. -/
noncomputable def humpMix (t : ℝ) : Measure (Fin 3) :=
  Real.toNNReal (1 - t) • uniform3 + Real.toNNReal t • hump3D

theorem humpMix_zero : humpMix 0 = uniform3 := by
  simp [humpMix]

theorem humpMix_one : humpMix 1 = hump3D := by
  simp [humpMix]

theorem toNNReal_add_toNNReal_eq_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.toNNReal (1 - t) + Real.toNNReal t = 1 := by
  rw [← Real.toNNReal_add (by linarith) ht0, sub_add_cancel, Real.toNNReal_one]

theorem isProbabilityMeasure_humpMix {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (humpMix t) :=
  isProbabilityMeasure_mixture uniform3 hump3D (toNNReal_add_toNNReal_eq_one ht0 ht1)

/-- Point masses along the path. -/
theorem humpMix_real_singleton {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Fin 3) :
    (humpMix t).real {x} = (1 - t) * (1 / 3) + t * hump3D.real {x} := by
  rw [humpMix, measureReal_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.coe_toReal, Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ ht0,
    ← measureReal_def, ← measureReal_def, uniform3_real_singleton]

/-- **The invisible information along the path**: `R(t) = KL(D_t ‖ Π(M_t))`. -/
noncomputable def humpResidual (t : ℝ) : ℝ≥0∞ :=
  klDiv (humpMix t)
    (responseProjection bdd_coordFeature uniform3 (dataMoment (humpMix t) coordFeature))

theorem humpResidual_zero : humpResidual 0 = 0 := by
  have h := responseProjection_mean_familyMeasure bdd_coordFeature uniform3 (0 : Fin 1 → ℝ)
  rw [familyMeasure_zero_eq bdd_coordFeature uniform3] at h
  unfold humpResidual
  rw [humpMix_zero]
  change klDiv uniform3
    (responseProjection bdd_coordFeature uniform3 (fun k ↦ ∫ x, coordFeature k x ∂uniform3)) = 0
  rw [h, klDiv_self]

theorem humpResidual_one : humpResidual 1 = 0 := by
  have h := responseProjection_mean_familyMeasure bdd_coordFeature uniform3
    (fun _ ↦ (-1 : ℝ) : Fin 1 → ℝ)
  unfold humpResidual
  rw [humpMix_one]
  have h' : responseProjection bdd_coordFeature uniform3
      (fun k ↦ ∫ x, coordFeature k x ∂hump3D) = hump3D := h
  change klDiv hump3D
    (responseProjection bdd_coordFeature uniform3 (fun k ↦ ∫ x, coordFeature k x ∂hump3D)) = 0
  rw [h', klDiv_self]

/-- **The hump**: strictly inside the path the invisible information is positive, because the
mixture is not a member of the exponential family. -/
theorem humpResidual_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < humpResidual t := by
  have hP := isProbabilityMeasure_humpMix ht0.le ht1.le
  have hrel : dataMoment (humpMix t) coordFeature ∈
      intrinsicInterior ℝ (momentBody uniform3 (fun _ ↦ (1 : ℝ)) coordFeature) := by
    rw [humpMix, dataMoment_mixture_eq_atlasPath bdd_coordFeature uniform3 hump3D ht0.le ht1.le,
      atlasPath_eq]
    exact segment_mem_intrinsicInterior bdd_coordFeature uniform3 hump3D
      hump3D_absolutelyContinuous ht0.le ht1
  unfold humpResidual
  rw [responseProjection_eq_familyMeasure_responseTheta bdd_coordFeature uniform3 hrel]
  set θ' := responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
    (one_integral_pos uniform3) bdd_coordFeature (dataMoment (humpMix t) coordFeature)
  have hQ : IsProbabilityMeasure (Pfam3 θ') :=
    isProbabilityMeasure_familyMeasure measurable_const (integrable_const 1) (fun _ ↦ one_pos)
      (one_integral_pos uniform3) measurable_const (M₀ := 0) (fun _ ↦ by simp) bdd_coordFeature
      (t := 1) _
  rw [pos_iff_ne_zero, Ne, klDiv_eq_zero_iff]
  intro heq
  -- point masses of the family member are log-linear
  have hfam : (Pfam3 θ').real {(1 : Fin 3)} * (Pfam3 θ').real {(1 : Fin 3)} =
      (Pfam3 θ').real {(0 : Fin 3)} * (Pfam3 θ').real {(2 : Fin 3)} :=
    (loglinear_mul (fun x ↦ (Pfam3 θ').real {x}) _ (-(θ' : Fin 1 → ℝ) 0)
      (fun x ↦ family3_real_singleton θ' x)).symm
  -- point masses of the mixture form a hump
  have hC : 0 < 1 / 3 / ∫ y, Real.exp (-1 * dirLoss coordFeature (fun _ ↦ (-1 : ℝ)) y) ∂uniform3 :=
    div_pos (by norm_num) (integral_exp_pos Integrable.of_finite)
  have hD : ∀ x, hump3D.real {x} =
      (1 / 3 / ∫ y, Real.exp (-1 * dirLoss coordFeature (fun _ ↦ (-1 : ℝ)) y) ∂uniform3) *
        Real.exp (1 * (x.val : ℝ)) := fun x ↦ by
    rw [hump3D, family3_real_singleton]
    norm_num
  have hlt := hump_mul (fun x ↦ (humpMix t).real {x}) ((1 - t) * (1 / 3))
    (t * (1 / 3 / ∫ y, Real.exp (-1 * dirLoss coordFeature (fun _ ↦ (-1 : ℝ)) y) ∂uniform3)) 1
    (by nlinarith) (mul_pos ht0 hC) one_ne_zero (fun x ↦ by
      rw [humpMix_real_singleton ht0.le ht1.le, hD x]
      ring)
  rw [heq] at hlt
  exact absurd hfam hlt.ne

/-- **The invisible information along the affine data path is neither antitone nor monotone**:
it vanishes at both ends and is positive in between. -/
theorem humpResidual_not_antitone : ¬ Antitone humpResidual ∧ ¬ Monotone humpResidual := by
  have hpos := humpResidual_pos (t := 1 / 2) (by norm_num) (by norm_num)
  constructor
  · intro h
    have := h (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [humpResidual_zero] at this
    exact absurd (le_antisymm this zero_le) hpos.ne'
  · intro h
    have := h (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    rw [humpResidual_one] at this
    exact absurd (le_antisymm this zero_le) hpos.ne'

end ThreePoint

end Laplace.Multi
