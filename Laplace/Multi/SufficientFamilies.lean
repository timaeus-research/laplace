/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.MonomialTests
import Laplace.Multi.DegreeRecovery

/-!
# Sufficient sub-families of observables

Which families of observables recover the degree-`k` Taylor tensor of a
loss at a nondegenerate minimum? The pairing limit
`tendsto_pairwise_normalized_moment_difference` says that, for two
certified losses with equal jets below `k`, the rescaled moment
difference at ANY test `φ` has leading coefficient
`-Cov_γ[φ, Q_k]`, where `Q_k` is the degree-`k` Taylor difference and
`γ = N(0, H⁻¹)`. Hence a family `S` of tests sees the degree-`k`
difference at the leading rate `q^(k-2)` exactly when some pairing
`Cov_γ[φ, Q_k]`, `φ ∈ S`, is nonzero.

This file packages that observation:

* `homogPolySpan d k`: the degree-`k` homogeneous polynomials on
  `EuclidD d`, as the span of the monomial words `monomialTest`; the
  degree-`k` Taylor difference of two losses lies in it.
* `gaussianCovariance` is linear in the second slot on this span, so the
  pairings assemble into an **observation operator**
  `pairingMap : homogPolySpan d k →ₗ[ℝ] (ι → ℝ)`.
* **B (iff)** `family_rates_iff_pairing_eq_zero`: the family's data are
  `o(q^(k-2))` for every test iff `Q_k` lies in the kernel of the
  observation operator.
* **A (sufficiency)** `iteratedFDeriv_recovery_of_family_rates`: if the
  observation operator is injective on `homogPolySpan d k`, the family's
  data at the rate identify the degree-`k` tensor. The monomial family is
  injective (`monomialTest_family_injective`), recovering
  `iteratedFDeriv_recovery_of_monomial_rates`.
* **C (obstruction)** `exists_kernel_of_finite_family`: in `d ≥ 2`, a
  family of `n` tests has a nonzero kernel direction in every degree
  `k ≥ n` (the `k + 1` two-coordinate monomials `x₀^(k-j) x₁^j` are
  linearly independent, and a linear map from a `(k+1)`-dimensional
  space to `ℝ^n` has nontrivial kernel). Combined with B:
  `finite_family_leading_rate_blind` — no fixed finite family sees every
  homogeneous perturbation at its first rate in every degree.

The obstruction is a *leading-rate* statement. A perturbation invisible
at order `q^(k-2)` can be visible at a later order (with `H = I`,
`L_ε = |x|²/2 + ε x₁³` against `φ = x₁²`: the cubic pairing vanishes by
parity, but the `ε²q²` term is `45 ε² q²`), so nothing here says that a
finite family cannot recover the jet from the *entire* expansions.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

variable {d k : ℕ}

/-! ### Closure lemmas for the certificates -/

theorem HasPolynomialGrowth.neg {f : EuclidD d → ℝ}
    (hf : HasPolynomialGrowth f) : HasPolynomialGrowth (fun x ↦ -f x) := by
  obtain ⟨C, n, hC, h⟩ := hf
  exact ⟨C, n, hC, fun x ↦ by rw [abs_neg]; exact h x⟩

theorem HasPolynomialGrowth.add {f g : EuclidD d → ℝ}
    (hf : HasPolynomialGrowth f) (hg : HasPolynomialGrowth g) :
    HasPolynomialGrowth (f + g) := by
  obtain ⟨C, n, hC, h⟩ := hf.sub hg.neg
  refine ⟨C, n, hC, fun x ↦ ?_⟩
  have := h x
  simpa [sub_neg_eq_add] using this

theorem HasPolynomialGrowth.const_smul {f : EuclidD d → ℝ}
    (hf : HasPolynomialGrowth f) (c : ℝ) :
    HasPolynomialGrowth (c • f) := by
  obtain ⟨C, n, hC, h⟩ := hf
  refine ⟨|c| * C, n, by positivity, fun x ↦ ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x) (abs_nonneg c)

theorem hasPolynomialGrowth_zero : HasPolynomialGrowth (0 : EuclidD d → ℝ) :=
  ⟨0, 0, le_rfl, fun x ↦ by simp⟩

theorem IsHomogeneousOfDegree.add {P Q : EuclidD d → ℝ}
    (hP : IsHomogeneousOfDegree k P) (hQ : IsHomogeneousOfDegree k Q) :
    IsHomogeneousOfDegree k (P + Q) := by
  intro a x
  simp only [Pi.add_apply, hP a x, hQ a x]
  ring

theorem IsHomogeneousOfDegree.const_smul {P : EuclidD d → ℝ}
    (hP : IsHomogeneousOfDegree k P) (c : ℝ) :
    IsHomogeneousOfDegree k (c • P) := by
  intro a x
  simp only [Pi.smul_apply, smul_eq_mul, hP a x]
  ring

theorem isHomogeneousOfDegree_zero :
    IsHomogeneousOfDegree k (0 : EuclidD d → ℝ) := by
  intro a x
  simp

/-! ### The degree-`k` homogeneous polynomials -/

/-- The degree-`k` homogeneous polynomials on `EuclidD d`: the span of
the monomial words `x ↦ ∏ j, x (m j)`, `m : Fin k → Fin d`. -/
def homogPolySpan (d k : ℕ) : Submodule ℝ (EuclidD d → ℝ) :=
  Submodule.span ℝ
    (Set.range (monomialTest : (Fin k → Fin d) → EuclidD d → ℝ))

theorem monomialTest_mem_homogPolySpan (m : Fin k → Fin d) :
    monomialTest m ∈ homogPolySpan d k :=
  Submodule.subset_span ⟨m, rfl⟩

theorem homogPolySpan_continuous {Q : EuclidD d → ℝ}
    (hQ : Q ∈ homogPolySpan d k) : Continuous Q := by
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact monomialTest_continuous m
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

theorem homogPolySpan_hasPolynomialGrowth {Q : EuclidD d → ℝ}
    (hQ : Q ∈ homogPolySpan d k) : HasPolynomialGrowth Q := by
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact monomialTest_hasPolynomialGrowth m
  | zero => exact hasPolynomialGrowth_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

theorem homogPolySpan_isHomogeneous {Q : EuclidD d → ℝ}
    (hQ : Q ∈ homogPolySpan d k) : IsHomogeneousOfDegree k Q := by
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact monomialTest_isHomogeneous m
  | zero => exact isHomogeneousOfDegree_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

/-- The degree-`k` Taylor difference of two losses is a degree-`k`
homogeneous polynomial: the diagonal expansion writes it as a
combination of monomial words. -/
theorem taylorDifference_mem_homogPolySpan (L₁ L₂ : EuclidD d → ℝ) :
    (fun x ↦ taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x) ∈
      homogPolySpan d k := by
  have hQ : (fun x ↦ taylorHomogeneousTerm k L₁ x -
      taylorHomogeneousTerm k L₂ x) =
      ∑ m : Fin k → Fin d,
        ((k.factorial : ℝ)⁻¹ *
          (iteratedFDeriv ℝ k L₁ 0
              (fun j ↦ EuclideanSpace.single (m j) (1 : ℝ)) -
            iteratedFDeriv ℝ k L₂ 0
              (fun j ↦ EuclideanSpace.single (m j) (1 : ℝ)))) •
          monomialTest m := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    unfold taylorHomogeneousTerm
    rw [diag_eq_sum_monomialTest (iteratedFDeriv ℝ k L₁ 0) x,
      diag_eq_sum_monomialTest (iteratedFDeriv ℝ k L₂ 0) x,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ ↦ by ring
  rw [hQ]
  exact Submodule.sum_mem _ fun m _ ↦
    Submodule.smul_mem _ _ (monomialTest_mem_homogPolySpan m)

/-! ### Linearity of the Gaussian covariance in the second slot -/

theorem gaussianExpectation_add {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {f g : EuclidD d → ℝ}
    (hfc : Continuous f) (hfg : HasPolynomialGrowth f)
    (hgc : Continuous g) (hgg : HasPolynomialGrowth g) :
    gaussianExpectation H (fun x ↦ f x + g x) =
      gaussianExpectation H f + gaussianExpectation H g := by
  unfold gaussianExpectation
  rw [← add_div]
  congr 1
  rw [← integral_add
    (integrable_mul_quadKernel_of_polynomialGrowth hH
      hfc.aestronglyMeasurable hfg)
    (integrable_mul_quadKernel_of_polynomialGrowth hH
      hgc.aestronglyMeasurable hgg)]
  congr 1
  funext x
  ring

theorem gaussianExpectation_const_mul {H : Matrix (Fin d) (Fin d) ℝ}
    (c : ℝ) (f : EuclidD d → ℝ) :
    gaussianExpectation H (fun x ↦ c * f x) =
      c * gaussianExpectation H f := by
  unfold gaussianExpectation
  rw [← mul_div_assoc, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only []
  ring

theorem gaussianCovariance_add_right {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {φ P Q : EuclidD d → ℝ}
    (hφc : Continuous φ) (hφg : HasPolynomialGrowth φ)
    (hPc : Continuous P) (hPg : HasPolynomialGrowth P)
    (hQc : Continuous Q) (hQg : HasPolynomialGrowth Q) :
    gaussianCovariance H φ (P + Q) =
      gaussianCovariance H φ P + gaussianCovariance H φ Q := by
  unfold gaussianCovariance
  have h2 := gaussianExpectation_add hH (f := fun x ↦ φ x * P x)
    (g := fun x ↦ φ x * Q x) (hφc.mul hPc) (hφg.mul hPg) (hφc.mul hQc) (hφg.mul hQg)
  have h1 : gaussianExpectation H (fun x ↦ φ x * (P + Q) x) =
      gaussianExpectation H (fun x ↦ φ x * P x) +
        gaussianExpectation H (fun x ↦ φ x * Q x) := by
    refine Eq.trans ?_ h2
    congr 1
    funext x
    simp only [Pi.add_apply]
    ring
  rw [h1, show gaussianExpectation H (P + Q) =
      gaussianExpectation H (fun x ↦ P x + Q x) from rfl,
    gaussianExpectation_add hH hPc hPg hQc hQg]
  ring

theorem gaussianCovariance_const_smul_right {H : Matrix (Fin d) (Fin d) ℝ}
    (φ Q : EuclidD d → ℝ) (c : ℝ) :
    gaussianCovariance H φ (c • Q) = c * gaussianCovariance H φ Q := by
  unfold gaussianCovariance
  have h1 : gaussianExpectation H (fun x ↦ φ x * (c • Q) x) =
      c * gaussianExpectation H (fun x ↦ φ x * Q x) := by
    rw [← gaussianExpectation_const_mul]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1, show gaussianExpectation H (c • Q) =
      gaussianExpectation H (fun x ↦ c * Q x) from rfl,
    gaussianExpectation_const_mul]
  ring

theorem gaussianCovariance_comm {H : Matrix (Fin d) (Fin d) ℝ}
    (f g : EuclidD d → ℝ) :
    gaussianCovariance H f g = gaussianCovariance H g f := by
  unfold gaussianCovariance
  rw [mul_comm (gaussianExpectation H f)]
  congr 2
  funext x
  ring

/-- **The observation operator** of a family of tests: pair a degree-`k`
homogeneous polynomial with every test under `γ = N(0, H⁻¹)`. -/
noncomputable def pairingMap {ι : Type*} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (φ : ι → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i)) :
    homogPolySpan d k →ₗ[ℝ] (ι → ℝ) where
  toFun Q := fun i ↦ gaussianCovariance H (φ i) Q
  map_add' Q R := by
    funext i
    simp only [Submodule.coe_add, Pi.add_apply]
    exact gaussianCovariance_add_right hH (hφc i) (hφg i)
      (homogPolySpan_continuous Q.2) (homogPolySpan_hasPolynomialGrowth Q.2)
      (homogPolySpan_continuous R.2) (homogPolySpan_hasPolynomialGrowth R.2)
  map_smul' c Q := by
    funext i
    simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply,
      smul_eq_mul]
    exact gaussianCovariance_const_smul_right (φ i) Q c

@[simp] theorem pairingMap_apply {ι : Type*} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (φ : ι → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i))
    (Q : homogPolySpan d k) (i : ι) :
    pairingMap hH φ hφc hφg Q i = gaussianCovariance H (φ i) Q := rfl

/-! ### B: the family sees the degree-`k` difference iff a pairing is nonzero -/

namespace HigherLaplaceDomain

variable {L₁ L₂ : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- **Observation characterisation** (B, iff): for certified losses with
equal jets below `k`, a family's rescaled moment differences are all
`o(q^(k-2))` iff every pairing of the family with the degree-`k` Taylor
difference vanishes. -/
theorem family_rates_iff_pairing_eq_zero (hk : 2 < k)
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    {ι : Type*} (φ : ι → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i)) :
    (∀ i, (fun q : ℝ ↦ A₁.rescaledMoment (φ i) q - A₂.rescaledMoment (φ i) q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2)) ↔
    (∀ i, gaussianCovariance H (φ i)
      (fun x ↦ taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x)
        = 0) := by
  constructor
  · intro h i
    have hlim := tendsto_pairwise_normalized_moment_difference hk A₁ A₂
      hlower (hφc i) (hφg i)
    have hzero := (h i).tendsto_div_nhds_zero
    exact neg_eq_zero.mp (tendsto_nhds_unique hlim hzero)
  · intro h i
    have hlim := tendsto_pairwise_normalized_moment_difference hk A₁ A₂
      hlower (hφc i) (hφg i)
    rw [h i, neg_zero] at hlim
    refine (isLittleO_iff_tendsto' ?_).mpr hlim
    filter_upwards [self_mem_nhdsWithin] with q hq hq0
    exact absurd hq0 (pow_ne_zero _ hq.ne')

/-! ### A: injective observation operators recover the tensor -/

/-- **Sufficient family** (A): if the observation operator of a family
of tests is injective on the degree-`k` homogeneous polynomials, then
`o(q^(k-2))` data at every test of the family identify the degree-`k`
derivative tensor. -/
theorem iteratedFDeriv_recovery_of_family_rates (hk : 2 < k)
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    {ι : Type*} (φ : ι → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i))
    (hinj : ∀ Q ∈ homogPolySpan d k,
      (∀ i, gaussianCovariance H (φ i) Q = 0) → Q = 0)
    (hdata : ∀ i,
      (fun q : ℝ ↦ A₁.rescaledMoment (φ i) q - A₂.rescaledMoment (φ i) q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2)) :
    iteratedFDeriv ℝ k L₁ 0 = iteratedFDeriv ℝ k L₂ 0 := by
  have hpair := (family_rates_iff_pairing_eq_zero hk A₁ A₂ hlower φ hφc hφg).mp
    hdata
  have hQ0 := hinj _ (taylorDifference_mem_homogPolySpan L₁ L₂) hpair
  have hdiag : ∀ x : EuclidD d,
      iteratedFDeriv ℝ k L₁ 0 (fun _ ↦ x) =
        iteratedFDeriv ℝ k L₂ 0 (fun _ ↦ x) := by
    intro x
    have hx := congrFun hQ0 x
    simp only [Pi.zero_apply] at hx
    unfold taylorHomogeneousTerm at hx
    have hfac : ((k.factorial : ℝ)⁻¹ : ℝ) ≠ 0 :=
      inv_ne_zero (by exact_mod_cast (Nat.factorial_ne_zero k))
    have hx' : (k.factorial : ℝ)⁻¹ *
        (iteratedFDeriv ℝ k L₁ 0 (fun _ ↦ x)) =
        (k.factorial : ℝ)⁻¹ *
        (iteratedFDeriv ℝ k L₂ 0 (fun _ ↦ x)) := by
      linarith [hx]
    exact mul_left_cancel₀ hfac hx'
  exact iteratedFDeriv_eq_of_diag_eq hsymm₁ hsymm₂ hdiag

/-- (A, kernel form) The same with injectivity phrased as a trivial
kernel of the observation operator. -/
theorem iteratedFDeriv_recovery_of_pairingMap_ker_eq_bot (hk : 2 < k)
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    {ι : Type*} (φ : ι → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i))
    (hker : LinearMap.ker (pairingMap (k := k) A₁.hH_posDef φ hφc hφg) = ⊥)
    (hdata : ∀ i,
      (fun q : ℝ ↦ A₁.rescaledMoment (φ i) q - A₂.rescaledMoment (φ i) q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2)) :
    iteratedFDeriv ℝ k L₁ 0 = iteratedFDeriv ℝ k L₂ 0 := by
  refine iteratedFDeriv_recovery_of_family_rates hk A₁ A₂ hlower hsymm₁ hsymm₂
    φ hφc hφg ?_ hdata
  intro Q hQ hpair
  have hmem : (⟨Q, hQ⟩ : homogPolySpan d k) ∈
      LinearMap.ker (pairingMap (k := k) A₁.hH_posDef φ hφc hφg) := by
    rw [LinearMap.mem_ker]
    funext i
    exact hpair i
  rw [hker, Submodule.mem_bot] at hmem
  exact congrArg Subtype.val hmem

end HigherLaplaceDomain

/-! ### The monomial family is injective (consistency with the seabed) -/

/-- Pairings against all monomial words of degree `k` control the
self-pairing of any degree-`k` homogeneous polynomial. -/
theorem gaussianCovariance_self_eq_zero_of_monomial_pairings
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {Q : EuclidD d → ℝ} (hQ : Q ∈ homogPolySpan d k)
    (hpair : ∀ m : Fin k → Fin d, gaussianCovariance H (monomialTest m) Q = 0) :
    gaussianCovariance H Q Q = 0 := by
  have hQc := homogPolySpan_continuous hQ
  have hQg := homogPolySpan_hasPolynomialGrowth hQ
  -- pairing with `Q` vanishes on the whole span, by induction on the first slot
  have key : ∀ P ∈ homogPolySpan d k, gaussianCovariance H P Q = 0 := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact hpair m
    | zero =>
      rw [gaussianCovariance_comm, show (0 : EuclidD d → ℝ) = (0 : ℝ) • Q by
        simp, gaussianCovariance_const_smul_right, zero_mul]
    | add x y hx hy ihx ihy =>
      rw [gaussianCovariance_comm, gaussianCovariance_add_right hH hQc hQg
        (homogPolySpan_continuous hx) (homogPolySpan_hasPolynomialGrowth hx)
        (homogPolySpan_continuous hy) (homogPolySpan_hasPolynomialGrowth hy),
        gaussianCovariance_comm Q x, gaussianCovariance_comm Q y, ihx, ihy, add_zero]
    | smul a x _ ihx =>
      rw [gaussianCovariance_comm, gaussianCovariance_const_smul_right,
        gaussianCovariance_comm Q x, ihx, mul_zero]
  exact key Q hQ

/-- **The monomial family is injective**: its observation operator has
trivial kernel on the degree-`k` homogeneous polynomials (`k > 0`). -/
theorem monomialTest_family_injective {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) (hk : 0 < k) :
    ∀ Q ∈ homogPolySpan d k,
      (∀ m : Fin k → Fin d, gaussianCovariance H (monomialTest m) Q = 0) →
        Q = 0 := by
  intro Q hQ hpair
  exact homogeneous_eq_zero_of_gaussianCovariance_self_eq_zero hH hk
    (homogPolySpan_continuous hQ) (homogPolySpan_hasPolynomialGrowth hQ)
    (homogPolySpan_isHomogeneous hQ)
    (gaussianCovariance_self_eq_zero_of_monomial_pairings hH hQ hpair)

/-! ### C: finite families have kernel directions in `d ≥ 2` -/

section Obstruction

/-- The two-coordinate word of type `j`: the first `k - j` slots read
coordinate `0`, the remaining `j` slots read coordinate `1`. Its monomial
is `x ↦ x₀^(k-j) x₁^j`. -/
def sliceWord (hd : 2 ≤ d) (j : Fin (k + 1)) : Fin k → Fin d :=
  fun i ↦ if (i : ℕ) < k - j then ⟨0, by omega⟩ else ⟨1, by omega⟩

/-- The probe point `(s, 1, 0, …, 0)`. -/
noncomputable def slicePoint (hd : 2 ≤ d) (s : ℝ) : EuclidD d :=
  EuclideanSpace.single ⟨0, by omega⟩ s + EuclideanSpace.single ⟨1, by omega⟩ 1

theorem slicePoint_apply_zero (hd : 2 ≤ d) (s : ℝ) :
    slicePoint hd s ⟨0, by omega⟩ = s := by
  unfold slicePoint
  simp [Fin.ext_iff]

theorem slicePoint_apply_one (hd : 2 ≤ d) (s : ℝ) :
    slicePoint hd s ⟨1, by omega⟩ = 1 := by
  unfold slicePoint
  simp [Fin.ext_iff]

/-- On the probe line the type-`j` slice monomial is `s^(k-j)`. -/
theorem monomialTest_sliceWord_slicePoint (hd : 2 ≤ d) (j : Fin (k + 1)) (s : ℝ) :
    monomialTest (sliceWord hd j) (slicePoint hd s) = s ^ (k - j) := by
  unfold monomialTest sliceWord
  have hval : ∀ i : Fin k,
      slicePoint hd s (if (i : ℕ) < k - j then (⟨0, by omega⟩ : Fin d)
        else ⟨1, by omega⟩) = if (i : ℕ) < k - j then s else 1 := by
    intro i
    by_cases hi : (i : ℕ) < k - j
    · rw [if_pos hi, if_pos hi]
      exact slicePoint_apply_zero hd s
    · rw [if_neg hi, if_neg hi]
      exact slicePoint_apply_one hd s
  simp only [hval]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  rw [Fin.card_filter_val_lt]
  omega

/-- The `k + 1` slice monomials are linearly independent as functions. -/
theorem linearIndependent_sliceMonomials (hd : 2 ≤ d) :
    LinearIndependent ℝ (fun j : Fin (k + 1) ↦ monomialTest (sliceWord hd j)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  -- evaluate the relation along the probe line
  have hev : ∀ s : ℝ, ∑ i : Fin (k + 1), g i * s ^ (k - i) = 0 := by
    intro s
    have := congrFun hg (slicePoint hd s)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      monomialTest_sliceWord_slicePoint] at this
    exact this
  -- the polynomial with these coefficients vanishes identically
  set p : Polynomial ℝ :=
    ∑ i : Fin (k + 1), Polynomial.C (g i) * Polynomial.X ^ (k - i) with hp
  have hp0 : p = 0 := by
    apply Polynomial.funext
    intro s
    rw [hp, Polynomial.eval_finsetSum, Polynomial.eval_zero]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    exact hev s
  -- read off the coefficient of `X^(k-j)`
  have hcoeff : p.coeff (k - j) = g j := by
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [if_neg]
      intro h
      apply hij
      ext
      have := j.isLt
      have := i.isLt
      omega
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [← hcoeff, hp0, Polynomial.coeff_zero]

instance : FiniteDimensional ℝ (homogPolySpan d k) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- The degree-`k` homogeneous polynomials have dimension at least
`k + 1` when `d ≥ 2`. -/
theorem le_finrank_homogPolySpan (hd : 2 ≤ d) :
    k + 1 ≤ Module.finrank ℝ (homogPolySpan d k) := by
  have hli : LinearIndependent ℝ
      (fun j : Fin (k + 1) ↦
        (⟨monomialTest (sliceWord hd j), monomialTest_mem_homogPolySpan _⟩ :
          homogPolySpan d k)) := by
    refine LinearIndependent.of_comp (homogPolySpan d k).subtype ?_
    exact linearIndependent_sliceMonomials hd
  have := hli.fintype_card_le_finrank
  simpa using this

/-- **Finite-family obstruction** (C): in `d ≥ 2`, any family of `n`
tests has a nonzero degree-`k` homogeneous polynomial in the kernel of
its observation operator as soon as `n ≤ k`. -/
theorem exists_kernel_of_finite_family (hd : 2 ≤ d) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {n : ℕ} (φ : Fin n → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i))
    (hnk : n ≤ k) :
    ∃ Q ∈ homogPolySpan d k, Q ≠ 0 ∧
      ∀ i, gaussianCovariance H (φ i) Q = 0 := by
  have hlt : Module.finrank ℝ (Fin n → ℝ) <
      Module.finrank ℝ (homogPolySpan d k) := by
    rw [Module.finrank_fin_fun]
    have := le_finrank_homogPolySpan (k := k) hd
    omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt
    (f := pairingMap (k := k) hH φ hφc hφg) hlt
  obtain ⟨Q, hQker, hQne⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨Q, Q.2, ?_, ?_⟩
  · intro h
    exact hQne (Submodule.coe_eq_zero.mp h)
  · intro i
    have := congrFun (LinearMap.mem_ker.mp hQker) i
    simpa using this

/-- **Leading-rate blindness of finite families** (B ∘ C): in `d ≥ 2`,
for every family of `n` tests and every degree `k ≥ max n 3`, there is a
nonzero degree-`k` homogeneous polynomial `Q` such that any two certified
losses with equal jets below `k` whose degree-`k` Taylor difference is
`Q` have all their family data `o(q^(k-2))`. -/
theorem finite_family_leading_rate_blind (hd : 2 ≤ d) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {n : ℕ} (φ : Fin n → EuclidD d → ℝ)
    (hφc : ∀ i, Continuous (φ i)) (hφg : ∀ i, HasPolynomialGrowth (φ i))
    (hk : 2 < k) (hnk : n ≤ k) :
    ∃ Q ∈ homogPolySpan d k, Q ≠ 0 ∧
      ∀ {L₁ L₂ : EuclidD d → ℝ}
        (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H),
        (∀ j < k, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0) →
        (fun x ↦ taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x) = Q →
        ∀ i, (fun q : ℝ ↦ A₁.rescaledMoment (φ i) q - A₂.rescaledMoment (φ i) q)
          =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2) := by
  obtain ⟨Q, hQ, hQne, hpair⟩ := exists_kernel_of_finite_family hd hH φ hφc hφg hnk
  refine ⟨Q, hQ, hQne, ?_⟩
  intro L₁ L₂ A₁ A₂ hlower hdiff
  refine (HigherLaplaceDomain.family_rates_iff_pairing_eq_zero hk A₁ A₂ hlower
    φ hφc hφg).mpr ?_
  intro i
  rw [hdiff]
  exact hpair i

end Obstruction

end Laplace.Multi
