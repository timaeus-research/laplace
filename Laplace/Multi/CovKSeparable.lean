/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.OneD.CovKAnharmonic
import Laplace.Multi.AmbientMoments

/-!
# E2's canonical experiment: eq:covK for the separable oscillator

`CovKAnharmonic` verified the note's eq:covK in one dimension. E2 runs "the primer's canonical
experiment" on the separable anharmonic oscillator `L(u) = ∑ᵢ ℓᵢ(uᵢ)` in `d = 10`; in the eigenframe
(`H`, `S`, `T` diagonal) the formula reads `∑ᵢ Bᵢᵢ/(2λᵢt²) − ∑ᵢ bᵢαᵢ/(2λᵢ²t²)`. Here:

* `gibbsExpectation_two_coord_separable`, `gibbsCov_coord_fun_separable`: observables of two
  distinct coordinates are independent, `Cov_L[f(uₖ), g(uᵢ)] = δₖᵢ Cov_{ℓₖ}[f, g]`;
* `prod_pow_single_pow`, `integrable_coord_pow_mul_separableAnharmonic`,
  `integrable_energy_coord_pow_separableAnharmonic`: the monomial integrability the bilinear
  expansions need;
* `gibbsCov_energy_probe_separableAnharmonic`: for an eigenframe-diagonal probe
  `ψ = ∑ᵢ (Bᵢ/2)uᵢ² + bᵢuᵢ`, `Cov_L[L, ψ] = ∑ᵢ Cov_{ℓᵢ}[ℓᵢ, (Bᵢ/2)x² + bᵢx]` exactly;
* `covK_separable_diag`: `t² Cov_L[L, ψ] → ∑ᵢ (Bᵢ/(2λᵢ) − bᵢαᵢ/(2λᵢ²))`, with `covKDiag`,
  `covKDiag_eq` (eq:covK in the eigenframe) and `covK_separable_diag_agree`;
* `covK_rotatedAnharmonic_diag`: the same in the note's rotated frame.
-/

open MeasureTheory Filter Topology Matrix Laplace.OneD

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-! ### Independence of distinct coordinates -/

section Independence

variable (ℓ : ι → ℝ → ℝ) (t : ℝ)

/-- **Observables of two distinct coordinates are independent**:
`⟨f(uᵢ) g(uⱼ)⟩_L = ⟨f⟩_{ℓᵢ} ⟨g⟩_{ℓⱼ}`. -/
theorem gibbsExpectation_two_coord_separable
    (hZ : ∀ m, _root_.Laplace.partitionFunction (ℓ m) t ≠ 0) {i j : ι} (hij : i ≠ j) (f g : ℝ → ℝ) :
    gibbsExpectation (separablePotential ℓ) t (fun u => f (u i) * g (u j)) =
      _root_.Laplace.gibbsExpectation (ℓ i) t f * _root_.Laplace.gibbsExpectation (ℓ j) t g := by
  classical
  have hji : j ≠ i := Ne.symm hij
  have h := gibbsExpectation_prod_separable ℓ t
    (fun m x => if m = i then f x else if m = j then g x else 1)
  have hL : (fun u : ι → ℝ => ∏ m, (if m = i then f (u m) else if m = j then g (u m) else 1)) =
      fun u => f (u i) * g (u j) := by
    funext u
    rw [Finset.prod_eq_mul i j hij (fun m _ hm => by simp [hm.1, hm.2])
      (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)]
    simp [hji]
  rw [hL] at h
  rw [h, Finset.prod_eq_mul i j hij (fun m _ hm => ?_)
    (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)]
  · simp [hji]
  · simp only [hm.1, hm.2, if_false]
    exact gibbsExpectation_one_of_ne_zero (hZ m)

/-- **Covariances of single-coordinate observables**: `Cov_L[f(uᵢ), g(uⱼ)] = δᵢⱼ Cov_{ℓᵢ}[f, g]`. -/
theorem gibbsCov_coord_fun_separable [DecidableEq ι]
    (hZ : ∀ m, _root_.Laplace.partitionFunction (ℓ m) t ≠ 0) (i j : ι) (f g : ℝ → ℝ) :
    gibbsCov (separablePotential ℓ) t (fun u => f (u i)) (fun u => g (u j)) =
      if i = j then _root_.Laplace.gibbsCov (ℓ i) t f g else 0 := by
  unfold gibbsCov _root_.Laplace.gibbsCov
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, gibbsExpectation_coord_separable ℓ t hZ i (fun x => f x * g x),
      gibbsExpectation_coord_separable ℓ t hZ i f, gibbsExpectation_coord_separable ℓ t hZ i g]
  · rw [if_neg hij, gibbsExpectation_two_coord_separable ℓ t hZ hij f g,
      gibbsExpectation_coord_separable ℓ t hZ i f, gibbsExpectation_coord_separable ℓ t hZ j g,
      sub_self]

end Independence

/-! ### Integrability of the mixed monomials -/

section Integrability

variable {lam alpha gamma : ι → ℝ}

theorem prod_pow_single_pow [DecidableEq ι] (u : ι → ℝ) (k : ι) (a : ℕ) :
    ∏ m, u m ^ (Pi.single k a : ι → ℕ) m = u k ^ a := by
  rw [Finset.prod_eq_single k (fun m _ hm => by simp [hm]) (by simp)]
  simp

/-- `uₖ^a uᵢ^m e^{−tL}` is integrable. -/
theorem integrable_coord_pow_mul_separableAnharmonic (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) (k i : ι) (a m : ℕ) :
    Integrable (fun u : ι → ℝ =>
      u k ^ a * u i ^ m * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  classical
  refine (integrable_monomial_separableAnharmonic hlam hgamma hdisc ht
    (Pi.single k a + Pi.single i m)).congr (Eventually.of_forall fun u => ?_)
  change (∏ n, u n ^ (Pi.single k a + Pi.single i m : ι → ℕ) n) * _ = _
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_pow_single_pow]

/-- `ℓₖ(uₖ) uᵢ^m e^{−tL}` is integrable. -/
theorem integrable_energy_coord_pow_separableAnharmonic (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) (k i : ι) (m : ℕ) :
    Integrable (fun u : ι → ℝ => anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * u i ^ m *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  have h2 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc ht k i 2 m
  have h3 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc ht k i 3 m
  have h4 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc ht k i 4 m
  refine (((h2.const_mul (lam k / 2)).add (h3.const_mul (alpha k / 6))).add
    (h4.const_mul (gamma k / 24))).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, anharmonicPotential]
  ring

end Integrability

/-! ### covK for eigenframe-diagonal probes -/

section Diagonal

variable {lam alpha gamma : ι → ℝ}

/-- **The energy–probe covariance splits into coordinates**: for `ψ = ∑ᵢ (Bᵢ/2)uᵢ² + bᵢuᵢ`,
`Cov_L[L, ψ] = ∑ᵢ Cov_{ℓᵢ}[ℓᵢ, (Bᵢ/2)x² + bᵢx]`. -/
theorem gibbsCov_energy_probe_separableAnharmonic (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) (B b : ι → ℝ) :
    gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (fun u => ∑ i, (B i / 2 * u i ^ 2 + b i * u i)) =
      ∑ k, _root_.Laplace.gibbsCov (anharmonicPotential (lam k) (alpha k) (gamma k)) t
        (anharmonicPotential (lam k) (alpha k) (gamma k)) (fun x => B k / 2 * x ^ 2 + b k * x) := by
  classical
  set L := separableAnharmonic lam alpha gamma with hL
  have hZ : ∀ m, _root_.Laplace.partitionFunction
      (anharmonicPotential (lam m) (alpha m) (gamma m)) t ≠ 0 :=
    fun m => (partitionFunction_anharmonic_pos (hlam m) (hgamma m) (hdisc m) ht).ne'
  -- integrability of the pieces
  have hE : ∀ k, Integrable (fun u : ι → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * Real.exp (-(t * L u))) := fun k => by
    have := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht k k 0
    simpa only [pow_zero, mul_one] using this
  have hP : ∀ i, Integrable (fun u : ι → ℝ => (B i / 2 * u i ^ 2 + b i * u i) *
      Real.exp (-(t * L u))) := fun i => by
    have h2 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc ht i i 2 0
    have h1 := integrable_coord_pow_mul_separableAnharmonic hlam hgamma hdisc ht i i 1 0
    refine ((h2.const_mul (B i / 2)).add (h1.const_mul (b i))).congr
      (Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply, pow_zero, mul_one, pow_one]
    ring
  have hEP : ∀ k i, Integrable (fun u : ι → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * (B i / 2 * u i ^ 2 + b i * u i) *
        Real.exp (-(t * L u))) := fun k i => by
    have h2 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht k i 2
    have h1 := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht k i 1
    refine ((h2.const_mul (B i / 2)).add (h1.const_mul (b i))).congr
      (Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply, pow_one]
    ring
  have hPsum : Integrable (fun u : ι → ℝ => (∑ i, (B i / 2 * u i ^ 2 + b i * u i)) *
      Real.exp (-(t * L u))) :=
    (integrable_finsetSum Finset.univ fun i _ => hP i).congr (Eventually.of_forall fun u => by
      simp only [Finset.sum_mul])
  have hEPsum : ∀ k, Integrable (fun u : ι → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
        (∑ i, (B i / 2 * u i ^ 2 + b i * u i)) * Real.exp (-(t * L u))) := fun k =>
    (integrable_finsetSum Finset.univ fun i _ => hEP k i).congr (Eventually.of_forall fun u => by
      simp only [Finset.mul_sum, Finset.sum_mul])
  -- the energy observable is the sum of coordinate energies
  have hLsum : (fun u : ι → ℝ => L u) =
      fun u => ∑ k, anharmonicPotential (lam k) (alpha k) (gamma k) (u k) := by
    funext u
    simp only [hL, separableAnharmonic, separablePotential]
  calc gibbsCov L t L (fun u => ∑ i, (B i / 2 * u i ^ 2 + b i * u i))
      = gibbsCov L t (fun u => ∑ k, anharmonicPotential (lam k) (alpha k) (gamma k) (u k))
          (fun u => ∑ i, (B i / 2 * u i ^ 2 + b i * u i)) := by rw [← hLsum]
    _ = ∑ k, gibbsCov L t (fun u => anharmonicPotential (lam k) (alpha k) (gamma k) (u k))
          (fun u => ∑ i, (B i / 2 * u i ^ 2 + b i * u i)) :=
        gibbsCov_finsetSum_left L t Finset.univ _ _ (fun k _ => hE k) (fun k _ => hEPsum k)
    _ = ∑ k, ∑ i, gibbsCov L t (fun u => anharmonicPotential (lam k) (alpha k) (gamma k) (u k))
          (fun u => B i / 2 * u i ^ 2 + b i * u i) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [gibbsCov_comm, gibbsCov_finsetSum_left L t Finset.univ _ _ (fun i _ => hP i)
          (fun i _ => (hEP k i).congr (Eventually.of_forall fun u => by ring))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [gibbsCov_comm]
    _ = ∑ k, ∑ i, if k = i then _root_.Laplace.gibbsCov (anharmonicPotential (lam k) (alpha k)
          (gamma k)) t (anharmonicPotential (lam k) (alpha k) (gamma k))
          (fun x => B i / 2 * x ^ 2 + b i * x) else 0 := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        have h := gibbsCov_coord_fun_separable
          (fun m => anharmonicPotential (lam m) (alpha m) (gamma m)) t hZ k i
          (anharmonicPotential (lam k) (alpha k) (gamma k)) (fun x => B i / 2 * x ^ 2 + b i * x)
        rw [hL, separableAnharmonic]
        exact h
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_eq_single k (fun i _ hi => if_neg (Ne.symm hi))
          (fun h => absurd (Finset.mem_univ k) h), if_pos rfl]

/-- **eq:covK for the separable oscillator, eigenframe-diagonal probes**:
`t² Cov_L[L, ∑ᵢ (Bᵢ/2)uᵢ² + bᵢuᵢ] → ∑ᵢ (Bᵢ/(2λᵢ) − bᵢαᵢ/(2λᵢ²))`. -/
theorem covK_separable_diag (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (B b : ι → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => ∑ i, (B i / 2 * u i ^ 2 + b i * u i)))
      atTop (𝓝 (∑ i, (B i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2)))) := by
  have h : Tendsto (fun t : ℝ => ∑ k, t ^ 2 * _root_.Laplace.gibbsCov
      (anharmonicPotential (lam k) (alpha k) (gamma k)) t
      (anharmonicPotential (lam k) (alpha k) (gamma k)) (fun x => B k / 2 * x ^ 2 + b k * x)) atTop
      (𝓝 (∑ i, (B i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2)))) :=
    tendsto_finsetSum _ fun k _ => covK_anharmonic (hlam k) (hgamma k) (hdisc k) (B k) (b k)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [gibbsCov_energy_probe_separableAnharmonic hlam hgamma hdisc ht B b, Finset.mul_sum]

/-- eq:covK in the eigenframe (`H = diag λ`, `S = diag(1/(λᵢt))`, `T = diag α`): the sum of the
one-dimensional four-term formulas. -/
noncomputable def covKDiag (lam alpha : ι → ℝ) (t : ℝ) (B b : ι → ℝ) : ℝ :=
  ∑ i, covKOneDim (lam i) (alpha i) t (B i) (b i)

theorem covKDiag_eq (hlam : ∀ i, lam i ≠ 0) {t : ℝ} (ht : t ≠ 0) (B b : ι → ℝ) :
    covKDiag lam alpha t B b =
      (∑ i, (B i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2))) / t ^ 2 := by
  unfold covKDiag
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => covKOneDim_eq (hlam i) ht _ _ _

/-- **The exact covariance agrees with eq:covK in the eigenframe**:
`t²(Cov_L[L, ψ] − covK(t)) → 0`. -/
theorem covK_separable_diag_agree (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (B b : ι → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * (gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => ∑ i, (B i / 2 * u i ^ 2 + b i * u i)) -
        covKDiag lam alpha t B b)) atTop (𝓝 0) := by
  have h := (covK_separable_diag hlam hgamma hdisc B b).sub_const
    (∑ i, (B i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2)))
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [covKDiag_eq (fun i => (hlam i).ne') ht.ne']
  have := ht.ne'
  field_simp

end Diagonal

/-! ### Off-diagonal probes and the full quadratic probe -/

section OffDiagonal

variable (ℓ : ι → ℝ → ℝ) (t : ℝ)

/-- **Observables of three distinct coordinates are independent.** -/
theorem gibbsExpectation_three_coord_separable
    (hZ : ∀ m, _root_.Laplace.partitionFunction (ℓ m) t ≠ 0) {i j k : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (f g h : ℝ → ℝ) :
    gibbsExpectation (separablePotential ℓ) t (fun u => f (u i) * g (u j) * h (u k)) =
      _root_.Laplace.gibbsExpectation (ℓ i) t f * _root_.Laplace.gibbsExpectation (ℓ j) t g *
        _root_.Laplace.gibbsExpectation (ℓ k) t h := by
  classical
  have hji : j ≠ i := Ne.symm hij
  have hki : k ≠ i := Ne.symm hik
  have hkj : k ≠ j := Ne.symm hjk
  have hp := gibbsExpectation_prod_separable ℓ t
    (fun m x => if m = i then f x else if m = j then g x else if m = k then h x else 1)
  -- a product with three distinguished factors
  have key : ∀ (F : ι → ℝ), (∀ m, m ≠ i → m ≠ j → m ≠ k → F m = 1) →
      ∏ m, F m = F i * F j * F k := by
    intro F hF
    rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ i),
      Finset.prod_eq_mul j k hjk (fun m hm hm' => hF m (Finset.ne_of_mem_erase hm) hm'.1 hm'.2)
        (fun h => absurd (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) h)
        (fun h => absurd (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩) h)]
    ring
  have hL : (fun u : ι → ℝ => ∏ m, (if m = i then f (u m) else if m = j then g (u m) else
      if m = k then h (u m) else 1)) = fun u => f (u i) * g (u j) * h (u k) := by
    funext u
    rw [key _ (fun m h1 h2 h3 => by simp [h1, h2, h3])]
    simp [hji, hki, hkj]
  rw [hL] at hp
  rw [hp, key _ (fun m h1 h2 h3 => by
    simp only [h1, h2, h3, if_false]
    exact gibbsExpectation_one_of_ne_zero (hZ m))]
  simp [hji, hki, hkj]

end OffDiagonal

section OffDiagonalAnharmonic

variable {lam alpha gamma : ι → ℝ}

/-- `uₖ^a uᵢ uⱼ e^{−tL}` is integrable. -/
theorem integrable_coord_pow_mul_mul_separableAnharmonic (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) (k i j : ι) (a : ℕ) :
    Integrable (fun u : ι → ℝ =>
      u k ^ a * u i * u j * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  classical
  refine (integrable_monomial_separableAnharmonic hlam hgamma hdisc ht
    (Pi.single k a + Pi.single i 1 + Pi.single j 1)).congr (Eventually.of_forall fun u => ?_)
  change (∏ n, u n ^ (Pi.single k a + Pi.single i 1 + Pi.single j 1 : ι → ℕ) n) * _ = _
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_pow_single_pow, pow_one]

/-- `ℓₖ(uₖ) uᵢ uⱼ e^{−tL}` is integrable. -/
theorem integrable_energy_coord_mul_separableAnharmonic (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) (k i j : ι) :
    Integrable (fun u : ι → ℝ => anharmonicPotential (lam k) (alpha k) (gamma k) (u k) *
      (u i * u j) * Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  have h2 := integrable_coord_pow_mul_mul_separableAnharmonic hlam hgamma hdisc ht k i j 2
  have h3 := integrable_coord_pow_mul_mul_separableAnharmonic hlam hgamma hdisc ht k i j 3
  have h4 := integrable_coord_pow_mul_mul_separableAnharmonic hlam hgamma hdisc ht k i j 4
  refine (((h2.const_mul (lam k / 2)).add (h3.const_mul (alpha k / 6))).add
    (h4.const_mul (gamma k / 24))).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, anharmonicPotential]
  ring

/-- **The off-diagonal energy–probe covariance, exactly**: for `i ≠ j`,
`Cov_L[L, uᵢuⱼ] = ⟨x⟩_{ℓⱼ} Cov_{ℓᵢ}[ℓᵢ, x] + ⟨x⟩_{ℓᵢ} Cov_{ℓⱼ}[ℓⱼ, x]`. -/
theorem gibbsCov_energy_pair_separableAnharmonic (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ} (ht : 0 < t) {i j : ι} (hij : i ≠ j) :
    gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (fun u => u i * u j) =
      _root_.Laplace.gibbsExpectation (anharmonicPotential (lam j) (alpha j) (gamma j)) t
          (fun x => x) *
        _root_.Laplace.gibbsCov (anharmonicPotential (lam i) (alpha i) (gamma i)) t
          (anharmonicPotential (lam i) (alpha i) (gamma i)) (fun x => x) +
      _root_.Laplace.gibbsExpectation (anharmonicPotential (lam i) (alpha i) (gamma i)) t
          (fun x => x) *
        _root_.Laplace.gibbsCov (anharmonicPotential (lam j) (alpha j) (gamma j)) t
          (anharmonicPotential (lam j) (alpha j) (gamma j)) (fun x => x) := by
  classical
  have hji : j ≠ i := Ne.symm hij
  set ℓ : ι → ℝ → ℝ := fun m => anharmonicPotential (lam m) (alpha m) (gamma m) with hℓ
  have hZ : ∀ m, _root_.Laplace.partitionFunction (ℓ m) t ≠ 0 :=
    fun m => (partitionFunction_anharmonic_pos (hlam m) (hgamma m) (hdisc m) ht).ne'
  have hE : ∀ k, Integrable (fun u : ι → ℝ => ℓ k (u k) *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := fun k => by
    have := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht k k 0
    simpa only [pow_zero, mul_one] using this
  have hEP : ∀ k, Integrable (fun u : ι → ℝ => ℓ k (u k) * (u i * u j) *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := fun k =>
    integrable_energy_coord_mul_separableAnharmonic hlam hgamma hdisc ht k i j
  have hLsum : (fun u : ι → ℝ => separableAnharmonic lam alpha gamma u) =
      fun u => ∑ k, ℓ k (u k) := by
    funext u
    simp only [hℓ, separableAnharmonic, separablePotential]
  -- the per-coordinate covariances
  have hterm : ∀ k, gibbsCov (separableAnharmonic lam alpha gamma) t (fun u => ℓ k (u k))
      (fun u => u i * u j) =
      if k = i then _root_.Laplace.gibbsExpectation (ℓ j) t (fun x => x) *
        _root_.Laplace.gibbsCov (ℓ i) t (ℓ i) (fun x => x)
      else if k = j then _root_.Laplace.gibbsExpectation (ℓ i) t (fun x => x) *
        _root_.Laplace.gibbsCov (ℓ j) t (ℓ j) (fun x => x)
      else 0 := by
    intro k
    unfold gibbsCov _root_.Laplace.gibbsCov
    have hpair : gibbsExpectation (separableAnharmonic lam alpha gamma) t (fun u => u i * u j) =
        _root_.Laplace.gibbsExpectation (ℓ i) t (fun x => x) *
          _root_.Laplace.gibbsExpectation (ℓ j) t (fun x => x) := by
      rw [separableAnharmonic]
      exact gibbsExpectation_two_coord_separable ℓ t hZ hij (fun x => x) (fun x => x)
    have hEk : gibbsExpectation (separableAnharmonic lam alpha gamma) t (fun u => ℓ k (u k)) =
        _root_.Laplace.gibbsExpectation (ℓ k) t (ℓ k) := by
      rw [separableAnharmonic]
      exact gibbsExpectation_coord_separable ℓ t hZ k (ℓ k)
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl, hpair, hEk]
      have : gibbsExpectation (separableAnharmonic lam alpha gamma) t
          (fun u => ℓ k (u k) * (u k * u j)) =
          _root_.Laplace.gibbsExpectation (ℓ k) t (fun x => ℓ k x * x) *
            _root_.Laplace.gibbsExpectation (ℓ j) t (fun x => x) := by
        rw [separableAnharmonic]
        have h := gibbsExpectation_two_coord_separable ℓ t hZ hij (fun x => ℓ k x * x) (fun x => x)
        convert h using 2
        funext u
        ring
      rw [this]
      ring
    · by_cases hkj : k = j
      · subst hkj
        rw [if_neg hki, if_pos rfl, hpair, hEk]
        have : gibbsExpectation (separableAnharmonic lam alpha gamma) t
            (fun u => ℓ k (u k) * (u i * u k)) =
            _root_.Laplace.gibbsExpectation (ℓ i) t (fun x => x) *
              _root_.Laplace.gibbsExpectation (ℓ k) t (fun x => ℓ k x * x) := by
          rw [separableAnharmonic]
          have h := gibbsExpectation_two_coord_separable ℓ t hZ hij (fun x => x)
            (fun x => ℓ k x * x)
          convert h using 2
          funext u
          ring
        rw [this]
        ring
      · rw [if_neg hki, if_neg hkj, hpair, hEk]
        have : gibbsExpectation (separableAnharmonic lam alpha gamma) t
            (fun u => ℓ k (u k) * (u i * u j)) =
            _root_.Laplace.gibbsExpectation (ℓ k) t (ℓ k) *
              _root_.Laplace.gibbsExpectation (ℓ i) t (fun x => x) *
              _root_.Laplace.gibbsExpectation (ℓ j) t (fun x => x) := by
          rw [separableAnharmonic]
          have h := gibbsExpectation_three_coord_separable ℓ t hZ hki hkj hij (ℓ k) (fun x => x)
            (fun x => x)
          convert h using 2
          funext u
          ring
        rw [this]
        ring
  calc gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (fun u => u i * u j)
      = gibbsCov (separableAnharmonic lam alpha gamma) t (fun u => ∑ k, ℓ k (u k))
          (fun u => u i * u j) := by rw [← hLsum]
    _ = ∑ k, gibbsCov (separableAnharmonic lam alpha gamma) t (fun u => ℓ k (u k))
          (fun u => u i * u j) :=
        gibbsCov_finsetSum_left _ t Finset.univ _ _ (fun k _ => hE k) (fun k _ => hEP k)
    _ = _ := by
        simp_rw [hterm]
        rw [Finset.sum_eq_add i j hij (fun k _ hk => by rw [if_neg hk.1, if_neg hk.2])
          (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h),
          if_pos rfl, if_neg hji, if_pos rfl]

/-- **Off-diagonal probe terms vanish at leading order**: for `i ≠ j`, `t² Cov_L[L, uᵢuⱼ] → 0`. -/
theorem covK_separable_offdiag (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {i j : ι} (hij : i ≠ j) :
    Tendsto (fun t : ℝ => t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i * u j)) atTop (𝓝 0) := by
  have h := ((firstMoment_tendsto_zero (hlam j) (hgamma j) (hdisc j)).mul
    (covK_anharmonic_lin (hlam i) (hgamma i) (hdisc i))).add
    ((firstMoment_tendsto_zero (hlam i) (hgamma i) (hdisc i)).mul
    (covK_anharmonic_lin (hlam j) (hgamma j) (hdisc j)))
  simp only [zero_mul, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [gibbsCov_energy_pair_separableAnharmonic hlam hgamma hdisc ht hij]
  ring

end OffDiagonalAnharmonic

/-! ### The full quadratic probe -/

section FullQuadratic

variable {lam alpha gamma : ι → ℝ}

/-- Covariance is additive in its first slot, given integrability of the pieces. -/
theorem gibbsCov_add_left_of_integrable (L : (ι → ℝ) → ℝ) (t : ℝ) (φ ψ χ : (ι → ℝ) → ℝ)
    (hφ : Integrable (fun w => φ w * Real.exp (-(t * L w))))
    (hψ : Integrable (fun w => ψ w * Real.exp (-(t * L w))))
    (hφχ : Integrable (fun w => φ w * χ w * Real.exp (-(t * L w))))
    (hψχ : Integrable (fun w => ψ w * χ w * Real.exp (-(t * L w)))) :
    gibbsCov L t (fun w => φ w + ψ w) χ = gibbsCov L t φ χ + gibbsCov L t ψ χ := by
  unfold gibbsCov
  have h1 : gibbsExpectation L t (fun w => (φ w + ψ w) * χ w) =
      gibbsExpectation L t (fun w => φ w * χ w) + gibbsExpectation L t (fun w => ψ w * χ w) := by
    rw [← gibbsExpectation_add_of_integrable L t _ _ hφχ hψχ]
    congr 1
    funext w
    ring
  rw [h1, gibbsExpectation_add_of_integrable L t _ _ hφ hψ]
  ring

/-- `L(u) ψ(u) e^{−tL}` is integrable as soon as each `ℓₖ(uₖ) ψ(u) e^{−tL}` is. -/
theorem integrable_energy_mul_separableAnharmonic {t : ℝ} (ψ : (ι → ℝ) → ℝ)
    (hψ : ∀ k, Integrable (fun u : ι → ℝ =>
      anharmonicPotential (lam k) (alpha k) (gamma k) (u k) * ψ u *
        Real.exp (-(t * separableAnharmonic lam alpha gamma u)))) :
    Integrable (fun u : ι → ℝ => separableAnharmonic lam alpha gamma u * ψ u *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := by
  refine (integrable_finsetSum Finset.univ fun k _ => hψ k).congr (Eventually.of_forall fun u => ?_)
  simp only [separableAnharmonic, separablePotential, Finset.sum_mul]

/-- `Cov_L[L, uᵢ^m] = Cov_{ℓᵢ}[ℓᵢ, x^m]`. -/
theorem gibbsCov_energy_coord_pow_separableAnharmonic (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) {t : ℝ}
    (ht : 0 < t) (i : ι) (m : ℕ) :
    gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (fun u => u i ^ m) =
      _root_.Laplace.gibbsCov (anharmonicPotential (lam i) (alpha i) (gamma i)) t
        (anharmonicPotential (lam i) (alpha i) (gamma i)) (fun x => x ^ m) := by
  classical
  set ℓ : ι → ℝ → ℝ := fun k => anharmonicPotential (lam k) (alpha k) (gamma k) with hℓ
  have hZ : ∀ k, _root_.Laplace.partitionFunction (ℓ k) t ≠ 0 :=
    fun k => (partitionFunction_anharmonic_pos (hlam k) (hgamma k) (hdisc k) ht).ne'
  have hE : ∀ k, Integrable (fun u : ι → ℝ => ℓ k (u k) *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := fun k => by
    have := integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht k k 0
    simpa only [pow_zero, mul_one] using this
  have hEP : ∀ k, Integrable (fun u : ι → ℝ => ℓ k (u k) * u i ^ m *
      Real.exp (-(t * separableAnharmonic lam alpha gamma u))) := fun k =>
    integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht k i m
  have hLsum : (fun u : ι → ℝ => separableAnharmonic lam alpha gamma u) =
      fun u => ∑ k, ℓ k (u k) := by
    funext u
    simp only [hℓ, separableAnharmonic, separablePotential]
  calc gibbsCov (separableAnharmonic lam alpha gamma) t (separableAnharmonic lam alpha gamma)
        (fun u => u i ^ m)
      = gibbsCov (separableAnharmonic lam alpha gamma) t (fun u => ∑ k, ℓ k (u k))
          (fun u => u i ^ m) := by rw [← hLsum]
    _ = ∑ k, gibbsCov (separableAnharmonic lam alpha gamma) t (fun u => ℓ k (u k))
          (fun u => u i ^ m) :=
        gibbsCov_finsetSum_left _ t Finset.univ _ _ (fun k _ => hE k) (fun k _ => hEP k)
    _ = ∑ k, if k = i then _root_.Laplace.gibbsCov (ℓ k) t (ℓ k) (fun x => x ^ m) else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have h := gibbsCov_coord_fun_separable ℓ t hZ k i (ℓ k) (fun x => x ^ m)
        rw [separableAnharmonic]
        exact h
    _ = _ := by
        rw [Finset.sum_eq_single i (fun k _ hk => if_neg hk)
          (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]

/-- `t² Cov_L[L, uᵢuⱼ] → δᵢⱼ/λᵢ`. -/
theorem covK_separable_pair [DecidableEq ι] (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i j : ι) :
    Tendsto (fun t : ℝ => t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i * u j)) atTop
      (𝓝 (if i = j then 1 / lam i else 0)) := by
  by_cases hij : i = j
  · rw [if_pos hij, hij]
    refine (covK_anharmonic_sq (hlam j) (hgamma j) (hdisc j)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← gibbsCov_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht j 2]
    simp only [sq]
  · rw [if_neg hij]
    exact covK_separable_offdiag hlam hgamma hdisc hij

/-- `t² Cov_L[L, uᵢ] → −αᵢ/(2λᵢ²)`. -/
theorem covK_separable_lin (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (i : ι) :
    Tendsto (fun t : ℝ => t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma) (fun u => u i)) atTop
      (𝓝 (-alpha i / (2 * lam i ^ 2))) := by
  refine (covK_anharmonic_lin (hlam i) (hgamma i) (hdisc i)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have h := gibbsCov_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht i 1
  simp only [pow_one] at h
  rw [h]

/-- **eq:covK for the separable oscillator, general quadratic probe**: for
`ψ = ½∑ᵢⱼ Bᵢⱼuᵢuⱼ + ∑ᵢ bᵢuᵢ`, `t² Cov_L[L, ψ] → ∑ᵢ (Bᵢᵢ/(2λᵢ) − bᵢαᵢ/(2λᵢ²))`.  Only the
eigenframe-diagonal part of `B` survives at leading order. -/
theorem covK_separable_quadratic (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
    (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (B : ι → ι → ℝ) (b : ι → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * gibbsCov (separableAnharmonic lam alpha gamma) t
        (separableAnharmonic lam alpha gamma)
        (fun u => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i)) atTop
      (𝓝 (∑ i, (B i i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2)))) := by
  classical
  set L := separableAnharmonic lam alpha gamma with hL
  have hsplit : ∀ t : ℝ, 0 < t → gibbsCov L t L
      (fun u => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) =
      ∑ p : ι × ι, B p.1 p.2 / 2 * gibbsCov L t L (fun u => u p.1 * u p.2) +
        ∑ i, b i * gibbsCov L t L (fun u => u i) := by
    intro t ht
    have hcm : ∀ i j, Integrable (fun u : ι → ℝ => u i * u j * Real.exp (-(t * L u))) :=
      fun i j => integrable_coord_mul_separableAnharmonic hlam hgamma hdisc ht i j
    have hc : ∀ i, Integrable (fun u : ι → ℝ => u i * Real.exp (-(t * L u))) :=
      fun i => integrable_coord_separableAnharmonic hlam hgamma hdisc ht i
    have hLcm : ∀ i j, Integrable (fun u : ι → ℝ =>
        L u * (u i * u j) * Real.exp (-(t * L u))) := fun i j =>
      integrable_energy_mul_separableAnharmonic _ fun k =>
        integrable_energy_coord_mul_separableAnharmonic hlam hgamma hdisc ht k i j
    have hLc : ∀ i, Integrable (fun u : ι → ℝ => L u * u i * Real.exp (-(t * L u))) := fun i =>
      integrable_energy_mul_separableAnharmonic (fun u => u i) fun k =>
        (integrable_energy_coord_pow_separableAnharmonic hlam hgamma hdisc ht k i 1).congr
          (Eventually.of_forall fun u => by simp only [pow_one])
    have hφP : ∀ p : ι × ι, Integrable (fun u : ι → ℝ =>
        B p.1 p.2 / 2 * (u p.1 * u p.2) * Real.exp (-(t * L u))) := fun p =>
      ((hcm p.1 p.2).const_mul (B p.1 p.2 / 2)).congr (Eventually.of_forall fun u => by ring)
    have hφPL : ∀ p : ι × ι, Integrable (fun u : ι → ℝ =>
        B p.1 p.2 / 2 * (u p.1 * u p.2) * L u * Real.exp (-(t * L u))) := fun p =>
      ((hLcm p.1 p.2).const_mul (B p.1 p.2 / 2)).congr (Eventually.of_forall fun u => by ring)
    have hφQ : ∀ i, Integrable (fun u : ι → ℝ => b i * u i * Real.exp (-(t * L u))) := fun i =>
      ((hc i).const_mul (b i)).congr (Eventually.of_forall fun u => by ring)
    have hφQL : ∀ i, Integrable (fun u : ι → ℝ => b i * u i * L u * Real.exp (-(t * L u))) :=
      fun i => ((hLc i).const_mul (b i)).congr (Eventually.of_forall fun u => by ring)
    have hP : Integrable (fun u : ι → ℝ =>
        (∑ p : ι × ι, B p.1 p.2 / 2 * (u p.1 * u p.2)) * Real.exp (-(t * L u))) :=
      (integrable_finsetSum (Finset.univ : Finset (ι × ι)) fun p _ => hφP p).congr
        (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
    have hQ : Integrable (fun u : ι → ℝ => (∑ i, b i * u i) * Real.exp (-(t * L u))) :=
      (integrable_finsetSum Finset.univ fun i _ => hφQ i).congr
        (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
    have hPL : Integrable (fun u : ι → ℝ =>
        (∑ p : ι × ι, B p.1 p.2 / 2 * (u p.1 * u p.2)) * L u * Real.exp (-(t * L u))) :=
      (integrable_finsetSum (Finset.univ : Finset (ι × ι)) fun p _ => hφPL p).congr
        (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
    have hQL : Integrable (fun u : ι → ℝ => (∑ i, b i * u i) * L u * Real.exp (-(t * L u))) :=
      (integrable_finsetSum Finset.univ fun i _ => hφQL i).congr
        (Eventually.of_forall fun u => by simp only [Finset.sum_mul])
    have hprobe : (fun u : ι → ℝ => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i) =
        fun u => (∑ p : ι × ι, B p.1 p.2 / 2 * (u p.1 * u p.2)) + ∑ i, b i * u i := by
      funext u
      congr 1
      exact (Fintype.sum_prod_type' fun a c => B a c / 2 * (u a * u c)).symm
    rw [hprobe, gibbsCov_comm, gibbsCov_add_left_of_integrable L t _ _ _ hP hQ hPL hQL,
      gibbsCov_finsetSum_left L t Finset.univ _ _ (fun p _ => hφP p) (fun p _ => hφPL p),
      gibbsCov_finsetSum_left L t Finset.univ _ _ (fun i _ => hφQ i) (fun i _ => hφQL i)]
    congr 1
    · exact Finset.sum_congr rfl fun p _ => by rw [gibbsCov_const_mul_left, gibbsCov_comm]
    · exact Finset.sum_congr rfl fun i _ => by rw [gibbsCov_const_mul_left, gibbsCov_comm]
  have h : Tendsto (fun t : ℝ =>
      ∑ p : ι × ι, B p.1 p.2 / 2 * (t ^ 2 * gibbsCov L t L (fun u => u p.1 * u p.2)) +
        ∑ i, b i * (t ^ 2 * gibbsCov L t L (fun u => u i))) atTop
      (𝓝 ((∑ p : ι × ι, B p.1 p.2 / 2 * (if p.1 = p.2 then 1 / lam p.1 else 0)) +
        ∑ i, b i * (-alpha i / (2 * lam i ^ 2)))) :=
    (tendsto_finsetSum (Finset.univ : Finset (ι × ι)) fun p _ =>
      (covK_separable_pair hlam hgamma hdisc p.1 p.2).const_mul (B p.1 p.2 / 2)).add
      (tendsto_finsetSum Finset.univ fun i _ =>
        (covK_separable_lin hlam hgamma hdisc i).const_mul (b i))
  have hlim : (∑ p : ι × ι, B p.1 p.2 / 2 * (if p.1 = p.2 then 1 / lam p.1 else 0)) +
      ∑ i, b i * (-alpha i / (2 * lam i ^ 2)) =
      ∑ i, (B i i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2)) := by
    rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [hsplit t ht, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun p _ => by ring
  · exact Finset.sum_congr rfl fun i _ => by ring

end FullQuadratic

/-! ### The note's frame -/

section Rotated

variable [DecidableEq ι] {lam alpha gamma : ι → ℝ} {Q : Matrix ι ι ℝ}

/-- **covK in the note's rotated frame**: the probe `∑ᵢ (Bᵢ/2)(Aw)ᵢ² + bᵢ(Aw)ᵢ`, quadratic in `w`,
has `t² Cov[L∘A, ψ∘A] → ∑ᵢ (Bᵢ/(2λᵢ) − bᵢαᵢ/(2λᵢ²))`. -/
theorem covK_rotatedAnharmonic_diag (hQ : Qᵀ * Q = 1) (c : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i) (B b : ι → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => ∑ i, (B i / 2 * affineFrame Q c w i ^ 2 + b i * affineFrame Q c w i))) atTop
      (𝓝 (∑ i, (B i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2)))) := by
  refine (covK_separable_diag hlam hgamma hdisc B b).congr' (Eventually.of_forall fun t => ?_)
  have hc := continuous_separableAnharmonic lam alpha gamma
  have hψ : Continuous fun u : ι → ℝ => ∑ i, (B i / 2 * u i ^ 2 + b i * u i) :=
    continuous_finsetSum _ fun i _ => by fun_prop
  have := gibbsCov_rotated_of_continuous hQ c hc hc hψ t
  simp only [rotatedAnharmonic]
  rw [← this]
  rfl

/-- **covK in the note's rotated frame, general quadratic probe**: for
`ψ(w) = ½∑ᵢⱼ Bᵢⱼ(Aw)ᵢ(Aw)ⱼ + ∑ᵢ bᵢ(Aw)ᵢ`, `t² Cov[L∘A, ψ] → ∑ᵢ (Bᵢᵢ/(2λᵢ) − bᵢαᵢ/(2λᵢ²))`. -/
theorem covK_rotatedAnharmonic_quadratic (hQ : Qᵀ * Q = 1) (c : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (hgamma : ∀ i, 0 < gamma i) (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
    (B : ι → ι → ℝ) (b : ι → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * gibbsCov (rotatedAnharmonic Q c lam alpha gamma) t
        (rotatedAnharmonic Q c lam alpha gamma)
        (fun w => ∑ i, ∑ j, B i j / 2 * (affineFrame Q c w i * affineFrame Q c w j) +
          ∑ i, b i * affineFrame Q c w i)) atTop
      (𝓝 (∑ i, (B i i / (2 * lam i) - b i * alpha i / (2 * lam i ^ 2)))) := by
  refine (covK_separable_quadratic hlam hgamma hdisc B b).congr'
    (Eventually.of_forall fun t => ?_)
  have hc := continuous_separableAnharmonic lam alpha gamma
  have hψ : Continuous fun u : ι → ℝ => ∑ i, ∑ j, B i j / 2 * (u i * u j) + ∑ i, b i * u i :=
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by fun_prop).add
      (continuous_finsetSum _ fun i _ => by fun_prop)
  have := gibbsCov_rotated_of_continuous hQ c hc hc hψ t
  simp only [rotatedAnharmonic]
  rw [← this]
  rfl

end Rotated

end Laplace.Multi
