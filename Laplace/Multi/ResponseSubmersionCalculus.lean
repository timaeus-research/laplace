/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseHorizontalLift
import Laplace.Multi.ResponseBilinearForm

/-!
# The submersion calculus of the response map in score space

Bounded measurable contrasts form a subspace `bddSpace X` of `X → ℝ` (the score space of
perturbations of the data law `ρ_g`). On it the forcing `k ↦ Cov_{ρ_g}(S, k)` and the differential
of the response map `k ↦ DΦ_g[k] = (Dm(Φ(g))|_W)⁻¹ Cov_{ρ_g}(S, k)` are linear maps into the
direction space `W` (`forcingLin`, `velLin`), and:

* **the invisible tangent space is the kernel**: `k ∈ ker DΦ_g ↔ Cov_{ρ_g}(S, k) = 0`
  (`mem_ker_velLin_iff`, `mem_ker_velLin_iff'`);
* **the differential is onto `W`** (`velLin_surjective`), with the canonical horizontal lift as a
  linear section (`horLin`, `velLin_horLin`);
* **score space splits**: `bddSpace = range(hor) ⊕ ker(DΦ_g)` (`isCompl_range_horLin_ker_velLin`),
  the horizontal projection `k ↦ hor(DΦ_g[k])` being a projection onto the horizontal contrasts;
* **orthogonality and Pythagoras**: horizontal contrasts are `ρ_g`-uncorrelated with invisible
  contrasts (`lawCov_horizontalLift_of_forcing_eq_zero`), the residual `k − hor(DΦ_g[k])` is
  invisible (`forcing_residual_eq_zero`), and for every contrast
  `Var_{ρ_g} k = ⟨C_{ρ_g}⁻¹ Dm v, Dm v⟩ + Var_{ρ_g}(k − hor v)` with `v = DΦ_g[k]`
  (`lawCov_self_eq_horizontal_add_residual`, `lawCov_self_eq_dotJ_add_residual`);
* **the quotient interpretation**: `bddSpace ⧸ ker(DΦ_g) ≃ W` (`velQuotEquiv`) — the response
  directions are the score directions modulo the invisible ones.

This packages `ResponseHorizontalLift` as a submersion: kernel, onto map, canonical lift,
orthogonal decomposition, quotient.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Space

variable (X : Type*) [MeasurableSpace X]

/-- **The score space**: bounded measurable contrasts, as a subspace of `X → ℝ`. -/
def bddSpace : Submodule ℝ (X → ℝ) where
  carrier := {f | Bdd f}
  add_mem' hf hg := hf.add hg
  zero_mem' := ⟨measurable_const, 0, fun _ ↦ by simp⟩
  smul_mem' c _ hf := hf.const_mul c

variable {X}

theorem mem_bddSpace {f : X → ℝ} : f ∈ bddSpace X ↔ Bdd f := Iff.rfl

end Space

section Calculus

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {g : X → ℝ} (hg : Bdd g)
include hS hg

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The chart derivative equivalence. -/
local notation "CDE" => chartDerivEquiv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The response of the data law. -/
local notation "Φg" => responseOf hS ν g

/-- The data law. -/
local notation "ρg" => ν.tilted g

omit [Nonempty X] [Fintype J] [Nonempty J] in
theorem forcing_sub {k ℓ : X → ℝ} (hk : Bdd k) (hℓ : Bdd ℓ) :
    forcing S ν g (fun x ↦ k x - ℓ x) = forcing S ν g k - forcing S ν g ℓ := by
  have e : (fun x ↦ k x - ℓ x) = fun x ↦ k x + (-1) * ℓ x := funext fun x ↦ by ring
  rw [e, forcing_add hS ν hg hk (hℓ.const_mul (-1)), forcing_const_mul, neg_one_smul,
    sub_eq_add_neg]

/-- **The forcing as a linear map** on the score space: `k ↦ Cov_{ρ_g}(S, k) ∈ W`. -/
noncomputable def forcingLin : bddSpace X →ₗ[ℝ] 𝕍 where
  toFun k := ⟨forcing S ν g k, forcing_mem_dirSpan hS ν hg k.2⟩
  map_add' k ℓ := Subtype.ext (by
    change forcing S ν g (fun x ↦ (k : X → ℝ) x + (ℓ : X → ℝ) x) =
      forcing S ν g (k : X → ℝ) + forcing S ν g (ℓ : X → ℝ)
    exact forcing_add hS ν hg k.2 ℓ.2)
  map_smul' c k := Subtype.ext (by
    change forcing S ν g (fun x ↦ c * (k : X → ℝ) x) = c • forcing S ν g (k : X → ℝ)
    exact forcing_const_mul ν c (k : X → ℝ))

theorem forcingLin_apply (k : bddSpace X) :
    (forcingLin hS ν hg k : J → ℝ) = forcing S ν g k := rfl

/-- **The differential of the response map** on the score space: `k ↦ DΦ_g[k]`. -/
noncomputable def velLin : bddSpace X →ₗ[ℝ] 𝕍 :=
  (CDE Φg).symm.toLinearEquiv.toLinearMap ∘ₗ forcingLin hS ν hg

theorem velLin_apply (k : bddSpace X) : velLin hS ν hg k = responseVel hS ν hg k.2 := rfl

/-- **The invisible tangent space is the kernel of the differential**:
`DΦ_g[k] = 0 ↔ Cov_{ρ_g}(S, k) = 0`. -/
theorem mem_ker_velLin_iff (k : bddSpace X) :
    k ∈ LinearMap.ker (velLin hS ν hg) ↔ forcing S ν g k = 0 := by
  rw [LinearMap.mem_ker, velLin_apply]
  simp only [responseVel]
  constructor
  · intro h
    have := congrArg (CDE Φg) h
    rw [ContinuousLinearEquiv.apply_symm_apply, map_zero] at this
    exact congrArg Subtype.val this
  · intro h
    have e : (⟨forcing S ν g k, forcing_mem_dirSpan hS ν hg k.2⟩ : 𝕍) = 0 := Subtype.ext h
    rw [e, map_zero]

/-- The kernel in covariance form: `k` is invisible iff it is uncorrelated with every statistic. -/
theorem mem_ker_velLin_iff' (k : bddSpace X) :
    k ∈ LinearMap.ker (velLin hS ν hg) ↔ ∀ i, lawCov (ρg) (S i) k = 0 := by
  rw [mem_ker_velLin_iff, funext_iff]
  rfl

/-- **The differential is onto the direction space.** -/
theorem velLin_surjective : Function.Surjective (velLin hS ν hg) := fun v ↦
  ⟨⟨horizontalLift hS ν hg v, bdd_horizontalLift hS ν hg v⟩, responseVel_horizontalLift hS ν hg v⟩

/-- **The canonical horizontal lift as a linear section** `W → bddSpace`. -/
noncomputable def horLin : 𝕍 →ₗ[ℝ] bddSpace X where
  toFun v := ⟨horizontalLift hS ν hg v, bdd_horizontalLift hS ν hg v⟩
  map_add' v w := Subtype.ext (by
    change horizontalLift hS ν hg (v + w) =
      fun x ↦ horizontalLift hS ν hg v x + horizontalLift hS ν hg w x
    simp only [horizontalLift, map_add, Submodule.coe_add, dirLoss_add])
  map_smul' c v := Subtype.ext (by
    change horizontalLift hS ν hg (c • v) = fun x ↦ c * horizontalLift hS ν hg v x
    simp only [horizontalLift, map_smul, Submodule.coe_smul, dirLoss_smul])

theorem horLin_apply (v : 𝕍) : (horLin hS ν hg v : X → ℝ) = horizontalLift hS ν hg v := rfl

/-- **The lift is a right inverse of the differential.** -/
theorem velLin_horLin (v : 𝕍) : velLin hS ν hg (horLin hS ν hg v) = v :=
  responseVel_horizontalLift hS ν hg v

theorem horLin_injective : Function.Injective (horLin hS ν hg) :=
  Function.LeftInverse.injective (velLin_horLin hS ν hg)

/-- The horizontal projection `k ↦ hor(DΦ_g[k])`. -/
noncomputable def horProj : bddSpace X →ₗ[ℝ] bddSpace X := horLin hS ν hg ∘ₗ velLin hS ν hg

theorem horProj_apply (k : bddSpace X) :
    (horProj hS ν hg k : X → ℝ) = horizontalLift hS ν hg (responseVel hS ν hg k.2) := rfl

/-- The horizontal projection is a projection onto the horizontal contrasts. -/
theorem isProj_horProj : LinearMap.IsProj (LinearMap.range (horLin hS ν hg)) (horProj hS ν hg) where
  map_mem k := ⟨velLin hS ν hg k, rfl⟩
  map_id := by
    rintro _ ⟨v, rfl⟩
    simp only [horProj, LinearMap.comp_apply, velLin_horLin]

/-- **Score space splits into horizontal contrasts and invisible contrasts.** -/
theorem isCompl_range_horLin_ker_velLin :
    IsCompl (LinearMap.range (horLin hS ν hg)) (LinearMap.ker (velLin hS ν hg)) := by
  have h := LinearMap.isCompl_of_proj (p := LinearMap.range (horLin hS ν hg))
    (f := (horLin hS ν hg).rangeRestrict ∘ₗ velLin hS ν hg) ?_
  · rwa [LinearMap.ker_comp, LinearMap.ker_rangeRestrict,
      LinearMap.ker_eq_bot.2 (horLin_injective hS ν hg), Submodule.comap_bot] at h
  · rintro ⟨_, v, rfl⟩
    apply Subtype.ext
    simp only [LinearMap.comp_apply, velLin_horLin, LinearMap.codRestrict_apply]

/-- **Horizontal contrasts are uncorrelated with invisible contrasts.** -/
theorem lawCov_horizontalLift_of_forcing_eq_zero (v : 𝕍) {ℓ : X → ℝ} (hℓ : Bdd ℓ)
    (h0 : forcing S ν g ℓ = 0) : lawCov (ρg) (horizontalLift hS ν hg v) ℓ = 0 := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  rw [horizontalLift, lawCov_dirLoss_left hS (ρg) _ ℓ hℓ]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [show lawCov (ρg) (S i) ℓ = forcing S ν g ℓ i from rfl, h0, Pi.zero_apply, mul_zero]

/-- **The residual of a contrast is invisible**: `Cov_{ρ_g}(S, k − hor(DΦ_g[k])) = 0`. -/
theorem forcing_residual_eq_zero {k : X → ℝ} (hk : Bdd k) :
    forcing S ν g (fun x ↦ k x - horizontalLift hS ν hg (responseVel hS ν hg hk) x) = 0 := by
  rw [forcing_sub hS ν hg hk (bdd_horizontalLift hS ν hg _), forcing_horizontalLift,
    forcing_eq_of_responseVel_eq hS ν hg hk rfl, sub_self]

/-- **Pythagoras in score space**:
`Var_{ρ_g} k = Var_{ρ_g} hor(DΦ_g[k]) + Var_{ρ_g}(k − hor(DΦ_g[k]))` for every bounded contrast,
at any data law. -/
theorem lawCov_self_eq_horizontal_add_residual {k : X → ℝ} (hk : Bdd k) :
    lawCov (ρg) k k =
      lawCov (ρg) (horizontalLift hS ν hg (responseVel hS ν hg hk))
        (horizontalLift hS ν hg (responseVel hS ν hg hk)) +
      lawCov (ρg) (fun x ↦ k x - horizontalLift hS ν hg (responseVel hS ν hg hk) x)
        (fun x ↦ k x - horizontalLift hS ν hg (responseVel hS ν hg hk) x) := by
  have := isProbabilityMeasure_tilted (integrable_exp_of_bdd ν hg)
  have hhor := bdd_horizontalLift hS ν hg (responseVel hS ν hg hk)
  have hres : Bdd fun x ↦ k x - horizontalLift hS ν hg (responseVel hS ν hg hk) x := hk.sub hhor
  have horth : lawCov (ρg) (horizontalLift hS ν hg (responseVel hS ν hg hk))
      (fun x ↦ k x - horizontalLift hS ν hg (responseVel hS ν hg hk) x) = 0 :=
    lawCov_horizontalLift_of_forcing_eq_zero hS ν hg _ hres (forcing_residual_eq_zero hS ν hg hk)
  calc lawCov (ρg) k k = lawCov (ρg)
        (fun x ↦ horizontalLift hS ν hg (responseVel hS ν hg hk) x +
          (k x - horizontalLift hS ν hg (responseVel hS ν hg hk) x))
        (fun x ↦ horizontalLift hS ν hg (responseVel hS ν hg hk) x +
          (k x - horizontalLift hS ν hg (responseVel hS ν hg hk) x)) := by
        congr 1 <;> funext x <;> ring
    _ = _ := by
        rw [lawCov_add_left_eq _ hhor hres (hhor.add hres), lawCov_add_right_eq _ hhor hres hhor,
          lawCov_add_right_eq _ hhor hres hres, horth,
          lawCov_comm (ρg) (fun x ↦ k x - horizontalLift hS ν hg (responseVel hS ν hg hk) x)
            (horizontalLift hS ν hg (responseVel hS ν hg hk)), horth]
        ring

/-- **The variance of a contrast through the covariance quotient**:
`Var_{ρ_g} k = ⟨C_{ρ_g}⁻¹ Dm(v), Dm(v)⟩ + Var_{ρ_g}(k − hor v)` with `v = DΦ_g[k]`. -/
theorem lawCov_self_eq_dotJ_add_residual {k : X → ℝ} (hk : Bdd k) :
    lawCov (ρg) k k =
      dotJ (((dataCovEquiv hS ν hg).symm (CDE Φg (responseVel hS ν hg hk)) : 𝕍) : J → ℝ)
        (CDE Φg (responseVel hS ν hg hk) : J → ℝ) +
      lawCov (ρg) (fun x ↦ k x - horizontalLift hS ν hg (responseVel hS ν hg hk) x)
        (fun x ↦ k x - horizontalLift hS ν hg (responseVel hS ν hg hk) x) := by
  rw [lawCov_self_eq_horizontal_add_residual hS ν hg hk, lawCov_horizontalLift_self]

/-- **The quotient interpretation**: response directions are score directions modulo invisible
ones, `bddSpace ⧸ ker(DΦ_g) ≃ W`. -/
noncomputable def velQuotEquiv :
    (bddSpace X ⧸ LinearMap.ker (velLin hS ν hg)) ≃ₗ[ℝ] 𝕍 :=
  LinearMap.quotKerEquivOfSurjective _ (velLin_surjective hS ν hg)

end Calculus

end Laplace.Multi
