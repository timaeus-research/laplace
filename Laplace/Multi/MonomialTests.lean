/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.DegreeRecovery

/-!
# Monomial test functions and the diagonal expansion

Preparation for the monomial-tests tide: the finitely many degree-`k`
monomial observables `x ↦ ∏ j, x (m j)` indexed by coordinate words
`m : Fin k → Fin d`, their certificates (continuity, polynomial
growth, homogeneity), the sum-of-singles decomposition of a Euclidean
vector, and the expansion of a continuous multilinear map's diagonal
into the monomial family. These are the ingredients that let the
tensor-recovery data hypotheses quantify over finitely many monomial
tests instead of every homogeneous observable.
-/

open Real Filter Topology Asymptotics

namespace Laplace.Multi

variable {d k : ℕ}

/-- The degree-`k` monomial observable attached to a coordinate word
`m : Fin k → Fin d`. -/
def monomialTest (m : Fin k → Fin d) : EuclidD d → ℝ :=
  fun x ↦ ∏ j : Fin k, x (m j)

/-- Coordinates are bounded by the Euclidean norm. -/
lemma euclid_abs_coord_le_norm (x : EuclidD d) (i : Fin d) :
    |x i| ≤ ‖x‖ := by
  rw [← Real.sqrt_sq_eq_abs, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc x i ^ 2 = ‖x i‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ j : Fin d, ‖x j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j : Fin d ↦ ‖x j‖ ^ 2)
          (fun j _ ↦ by positivity) (Finset.mem_univ i)

theorem monomialTest_continuous (m : Fin k → Fin d) :
    Continuous (monomialTest m) := by
  unfold monomialTest
  exact continuous_finset_prod _ fun j _ ↦
    PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) (m j)

theorem monomialTest_hasPolynomialGrowth (m : Fin k → Fin d) :
    HasPolynomialGrowth (monomialTest m) := by
  refine ⟨1, k, zero_le_one, fun x ↦ ?_⟩
  unfold monomialTest
  rw [Finset.abs_prod, one_mul]
  calc ∏ j : Fin k, |x (m j)|
      ≤ ∏ _j : Fin k, ‖x‖ :=
        Finset.prod_le_prod (fun j _ ↦ abs_nonneg _)
          (fun j _ ↦ euclid_abs_coord_le_norm x (m j))
    _ = ‖x‖ ^ k := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ 1 + ‖x‖ ^ k := by linarith [pow_nonneg (norm_nonneg x) k]

theorem monomialTest_isHomogeneous (m : Fin k → Fin d) :
    IsHomogeneousOfDegree k (monomialTest m) := by
  intro a x
  unfold monomialTest
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Sum-of-singles decomposition of a Euclidean vector. -/
theorem euclid_eq_sum_single (x : EuclidD d) :
    x = ∑ i : Fin d, x i • EuclideanSpace.single i (1 : ℝ) := by
  have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
  simp only [EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply] at h
  exact h.symm

/-- **Diagonal expansion**: the diagonal of a continuous multilinear
map on `EuclidD d` is the finite linear combination of monomial tests
with basis-evaluation coefficients. -/
theorem diag_eq_sum_monomialTest
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ EuclidD d) ℝ)
    (x : EuclidD d) :
    T (fun _ ↦ x) =
      ∑ m : Fin k → Fin d, monomialTest m x *
        T (fun j ↦ EuclideanSpace.single (m j) (1 : ℝ)) := by
  have hexp := T.toMultilinearMap.map_sum
    (g := fun (_ : Fin k) (i : Fin d) ↦
      x i • EuclideanSpace.single i (1 : ℝ))
  have hsmul : ∀ m : Fin k → Fin d,
      T.toMultilinearMap (fun j ↦ x (m j) •
        EuclideanSpace.single (m j) (1 : ℝ)) =
      monomialTest m x *
        T (fun j ↦ EuclideanSpace.single (m j) (1 : ℝ)) := by
    intro m
    rw [T.toMultilinearMap.map_smul_univ
      (fun j ↦ x (m j))
      (fun j ↦ EuclideanSpace.single (m j) (1 : ℝ))]
    simp only [ContinuousMultilinearMap.coe_coe, smul_eq_mul]
    rfl
  calc T (fun _ ↦ x)
      = T.toMultilinearMap (fun _ : Fin k ↦
          ∑ i : Fin d, x i • EuclideanSpace.single i (1 : ℝ)) := by
        rw [show T.toMultilinearMap (fun _ : Fin k ↦
            ∑ i : Fin d, x i • EuclideanSpace.single i (1 : ℝ)) =
            T (fun _ : Fin k ↦
            ∑ i : Fin d, x i • EuclideanSpace.single i (1 : ℝ)) from
          rfl, ← euclid_eq_sum_single x]
    _ = ∑ m : Fin k → Fin d, T.toMultilinearMap
          (fun j ↦ x (m j) •
            EuclideanSpace.single (m j) (1 : ℝ)) := hexp
    _ = ∑ m : Fin k → Fin d, monomialTest m x *
          T (fun j ↦ EuclideanSpace.single (m j) (1 : ℝ)) :=
        Finset.sum_congr rfl fun m _ ↦ hsmul m

namespace HigherLaplaceDomain

variable {L₁ L₂ : EuclidD d → ℝ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The rescaled posterior moment is linear over finite weighted sums
of tests (the denominator is test-independent, so normalization does
not obstruct linearity). -/
theorem rescaledMoment_finset_sum {k : ℕ}
    (A : HigherLaplaceDomain k L₁ H) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (P : ι → EuclidD d → ℝ)
    (hP_cont : ∀ i, Continuous (P i))
    (hP_growth : ∀ i, HasPolynomialGrowth (P i))
    {q : ℝ} (hq : 0 < q) :
    A.rescaledMoment (fun x ↦ ∑ i ∈ s, c i * P i x) q =
      ∑ i ∈ s, c i * A.rescaledMoment (P i) q := by
  have hS_meas : MeasurableSet {x : EuclidD d | q • x ∈ A.U} :=
    (measurable_const_smul q) A.measurableSet_U
  have hint : ∀ i ∈ s, MeasureTheory.Integrable
      (fun x : EuclidD d ↦
        A.toLocalLaplaceDomain.integrand (P i) q x) := by
    intro i _
    have h := integrable_indicator_slice A (hP_cont i)
      (hP_growth i) hq hS_meas fun x hx ↦ hx
    exact h
  have hnum : ∫ x : EuclidD d, A.toLocalLaplaceDomain.integrand
      (fun y ↦ ∑ i ∈ s, c i * P i y) q x =
      ∑ i ∈ s, c i * ∫ x : EuclidD d,
        A.toLocalLaplaceDomain.integrand (P i) q x := by
    have hpt : (fun x : EuclidD d ↦
        A.toLocalLaplaceDomain.integrand
          (fun y ↦ ∑ i ∈ s, c i * P i y) q x) =
        fun x : EuclidD d ↦ ∑ i ∈ s, c i *
          A.toLocalLaplaceDomain.integrand (P i) q x := by
      funext x
      unfold LocalLaplaceDomain.integrand
      by_cases hmem : x ∈ {x : EuclidD d | q • x ∈ A.U}
      · rw [Set.indicator_of_mem hmem]
        simp only [Set.indicator_of_mem hmem]
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      · rw [Set.indicator_of_notMem hmem]
        symm
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        rw [Set.indicator_of_notMem hmem, mul_zero]
    rw [hpt]
    rw [MeasureTheory.integral_finset_sum s
      (fun i hi ↦ (hint i hi).const_mul (c i))]
    exact Finset.sum_congr rfl fun i _ ↦
      MeasureTheory.integral_const_mul _ _
  unfold rescaledMoment
  rw [hnum, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ ↦ mul_div_assoc _ _ _

/-- **Single-degree tensor recovery from monomial data** (J6-prime):
`o(q^(k-2))` rescaled moment data at the finitely many degree-`k`
monomial tests already identifies the `k`-th derivative tensor. -/
theorem iteratedFDeriv_recovery_of_monomial_rates {k : ℕ}
    (hk : 2 < k)
    (A₁ : HigherLaplaceDomain k L₁ H) (A₂ : HigherLaplaceDomain k L₂ H)
    (hlower : ∀ j < k,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata : ∀ m : Fin k → Fin d,
      (fun q : ℝ ↦ A₁.rescaledMoment (monomialTest m) q -
        A₂.rescaledMoment (monomialTest m) q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2)) :
    iteratedFDeriv ℝ k L₁ 0 = iteratedFDeriv ℝ k L₂ 0 := by
  refine iteratedFDeriv_recovery_of_taylorDifference_rate hk A₁ A₂
    hlower hsymm₁ hsymm₂ ?_
  set c : (Fin k → Fin d) → ℝ := fun m ↦
    (k.factorial : ℝ)⁻¹ *
      (iteratedFDeriv ℝ k L₁ 0
          (fun j ↦ EuclideanSpace.single (m j) (1 : ℝ)) -
        iteratedFDeriv ℝ k L₂ 0
          (fun j ↦ EuclideanSpace.single (m j) (1 : ℝ)))
    with hc_def
  have hQfun : (fun x : EuclidD d ↦ taylorHomogeneousTerm k L₁ x -
      taylorHomogeneousTerm k L₂ x) =
      fun x : EuclidD d ↦
        ∑ m : Fin k → Fin d, c m * monomialTest m x := by
    funext x
    unfold taylorHomogeneousTerm
    rw [diag_eq_sum_monomialTest (iteratedFDeriv ℝ k L₁ 0) x,
      diag_eq_sum_monomialTest (iteratedFDeriv ℝ k L₂ 0) x,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [hc_def]
    ring
  have hsum : (fun q : ℝ ↦ ∑ m : Fin k → Fin d, c m *
      (A₁.rescaledMoment (monomialTest m) q -
        A₂.rescaledMoment (monomialTest m) q))
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2) :=
    Asymptotics.IsLittleO.sum fun m _ ↦
      (hdata m).const_mul_left (c m)
  refine hsum.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [hQfun,
    rescaledMoment_finset_sum A₁ Finset.univ c monomialTest
      (fun m ↦ monomialTest_continuous m)
      (fun m ↦ monomialTest_hasPolynomialGrowth m) hq,
    rescaledMoment_finset_sum A₂ Finset.univ c monomialTest
      (fun m ↦ monomialTest_continuous m)
      (fun m ↦ monomialTest_hasPolynomialGrowth m) hq,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ ↦ by ring

/-- **Finite-jet recovery from monomial data** (J7-prime): moment
data at the finitely many monomial tests of each degree up to `N`
identifies the full jet through order `N`. -/
theorem finite_jet_recovery_of_monomial_rates {N : ℕ}
    (A : ∀ k, 2 < k → k ≤ N → HigherLaplaceDomain k L₁ H)
    (B : ∀ k, 2 < k → k ≤ N → HigherLaplaceDomain k L₂ H)
    (hbase : ∀ j < 3,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : ∀ k, 2 < k → k ≤ N →
      (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 2 < k → k ≤ N →
      (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata : ∀ k (h2 : 2 < k) (hN : k ≤ N), ∀ m : Fin k → Fin d,
      (fun q : ℝ ↦ (A k h2 hN).rescaledMoment (monomialTest m) q -
        (B k h2 hN).rescaledMoment (monomialTest m) q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2)) :
    ∀ j, j ≤ N →
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjN
    by_cases hj3 : j < 3
    · exact hbase j hj3
    · have h2j : 2 < j := by omega
      exact iteratedFDeriv_recovery_of_monomial_rates h2j
        (A j h2j hjN) (B j h2j hjN)
        (fun i hi ↦ ih i hi (by omega))
        (hsymm₁ j h2j hjN) (hsymm₂ j h2j hjN)
        (hdata j h2j hjN)

/-- **Smooth-jet recovery from monomial data** (J7-prime, all
orders): per-degree monomial moment data at every degree identifies
every derivative tensor at the origin. -/
theorem smooth_jet_recovery_of_monomial_rates
    (A : ∀ k, 2 < k → HigherLaplaceDomain k L₁ H)
    (B : ∀ k, 2 < k → HigherLaplaceDomain k L₂ H)
    (hbase : ∀ j < 3,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (hsymm₁ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (hsymm₂ : ∀ k, 2 < k → (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdata : ∀ k (h2 : 2 < k), ∀ m : Fin k → Fin d,
      (fun q : ℝ ↦ (A k h2).rescaledMoment (monomialTest m) q -
        (B k h2).rescaledMoment (monomialTest m) q)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (k - 2)) :
    ∀ j, iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0 := by
  intro j
  exact finite_jet_recovery_of_monomial_rates (N := j)
    (fun k h2 _ ↦ A k h2) (fun k h2 _ ↦ B k h2)
    hbase
    (fun k h2 _ ↦ hsymm₁ k h2) (fun k h2 _ ↦ hsymm₂ k h2)
    (fun k h2 hN ↦ hdata k h2)
    j le_rfl

end HigherLaplaceDomain

end Laplace.Multi
