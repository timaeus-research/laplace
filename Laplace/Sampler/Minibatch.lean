/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.FullStep

/-!
# Sampling without replacement: the finite population correction behind E8

A minibatch is a uniformly random `m`-subset `B` of the `n` samples. For any bilinear
`β : V →ₗ[ℝ] V →ₗ[ℝ] W` and `a : Fin n → V` with population mean `ā` and batch mean
`mean_B a = (1/m) ∑_{i∈B} aᵢ`,

  `E_B[β(mean_B a − ā, mean_B a − ā)] = ((1 − m/n)/(m(n−1))) ∑ᵢ β(aᵢ − ā, aᵢ − ā)`

(`fpc_bilinear`), Cochran's finite population correction. The two E8 constants of the sanity note
follow: the minibatch gradient-noise covariance is `C_g = (1/m)(1 − m/n) S²` with `S²` the `n − 1`
sample covariance of the per-sample gradients (`minibatch_gradient_cov`), and the full law's
state-dependent term is `((1 − m/n)/(m(n−1))) ∑ᵢ (Hᵢ − H) Σ (Hᵢ − H)ᵀ = c · stateTerm`
(`minibatch_hessian_term`), the coefficient `minibatchCoeff` of `FullStep.lean`.

The counting is elementary: `C(n−1, m−1)` subsets contain a given sample and `C(n−2, m−2)`
contain a given pair (`0` when `m = 1`); the off-diagonal sum of a centred family is minus its
diagonal.
-/

open Finset Matrix

namespace Laplace.Sampler

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-! ### Means -/

/-- The batch mean `(1/m) ∑_{i∈B} aᵢ`. -/
noncomputable def batchMean {n : ℕ} (m : ℕ) (a : Fin n → V) (B : Finset (Fin n)) : V :=
  (m : ℝ)⁻¹ • ∑ i ∈ B, a i

/-- The population mean `(1/n) ∑ᵢ aᵢ`. -/
noncomputable def popMean {n : ℕ} (a : Fin n → V) : V := (n : ℝ)⁻¹ • ∑ i, a i

theorem sum_sub_popMean {n : ℕ} (hn : 0 < n) (a : Fin n → V) :
    ∑ i, (a i - popMean a) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, popMean,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), one_smul, sub_self]

theorem batchMean_sub_popMean {n m : ℕ} (hm : 0 < m) (a : Fin n → V) {B : Finset (Fin n)}
    (hB : B ∈ powersetCard m (univ : Finset (Fin n))) :
    batchMean m a B - popMean a = (m : ℝ)⁻¹ • ∑ i ∈ B, (a i - popMean a) := by
  have hcard : #B = m := (Finset.mem_powersetCard.mp hB).2
  rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0), one_smul, batchMean]

/-! ### Counting subsets -/

theorem card_powersetCard_mem {n m : ℕ} (i : Fin n) (hm : 1 ≤ m) :
    #((powersetCard m (univ : Finset (Fin n))).filter (fun B => i ∈ B)) =
      (n - 1).choose (m - 1) := by
  have h := Finset.card_filter_powersetCard_subset {i} univ m (Finset.subset_univ _)
    (by simpa using hm)
  rw [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at h
  rw [← h]
  congr 1
  exact Finset.filter_congr fun B _ => Finset.singleton_subset_iff.symm

theorem card_powersetCard_pair {n m : ℕ} {i j : Fin n} (hij : i ≠ j) :
    #((powersetCard m (univ : Finset (Fin n))).filter (fun B => i ∈ B ∧ j ∈ B)) =
      if 2 ≤ m then (n - 2).choose (m - 2) else 0 := by
  split_ifs with h2
  · have h := Finset.card_filter_powersetCard_subset {i, j} univ m (Finset.subset_univ _)
      (by rw [Finset.card_pair hij]; exact h2)
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hij] at h
    rw [← h]
    congr 1
    exact Finset.filter_congr fun B _ => by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro B hB hij'
    have hsub : ({i, j} : Finset (Fin n)) ⊆ B :=
      Finset.insert_subset hij'.1 (Finset.singleton_subset_iff.mpr hij'.2)
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hij, (Finset.mem_powersetCard.mp hB).2] at this
    omega

/-! ### Double counting -/

omit [Module ℝ V] in
theorem sum_eq_sum_ite_mem {n : ℕ} (B : Finset (Fin n)) (F : Fin n → V) :
    ∑ i ∈ B, F i = ∑ i, if i ∈ B then F i else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

omit [Module ℝ V] in
/-- `∑_B ∑_{i∈B} f i = C(n−1, m−1) ∑ᵢ f i`. -/
theorem sum_powersetCard_sum {n m : ℕ} (hm : 1 ≤ m) (f : Fin n → V) :
    ∑ B ∈ powersetCard m (univ : Finset (Fin n)), ∑ i ∈ B, f i =
      ((n - 1).choose (m - 1)) • ∑ i, f i := by
  rw [Finset.sum_congr rfl fun B _ => sum_eq_sum_ite_mem B f, Finset.sum_comm]
  simp_rw [← Finset.sum_filter, Finset.sum_const, card_powersetCard_mem _ hm]
  rw [Finset.smul_sum]

omit [Module ℝ V] in
/-- `∑_B ∑_{i,j∈B} g i j = C(n−1,m−1) ∑ᵢ g i i + C(n−2,m−2) ∑_{i≠j} g i j`
(pair count `0` at `m = 1`). -/
theorem sum_powersetCard_sum_sum {n m : ℕ} (hm : 1 ≤ m) (g : Fin n → Fin n → V) :
    ∑ B ∈ powersetCard m (univ : Finset (Fin n)), ∑ i ∈ B, ∑ j ∈ B, g i j =
      ((n - 1).choose (m - 1)) • ∑ i, g i i +
        (if 2 ≤ m then (n - 2).choose (m - 2) else 0) • ∑ i, ∑ j ∈ univ.erase i, g i j := by
  have hind : ∀ B : Finset (Fin n), ∑ i ∈ B, ∑ j ∈ B, g i j =
      ∑ i, ∑ j, if i ∈ B ∧ j ∈ B then g i j else 0 := fun B => by
    rw [sum_eq_sum_ite_mem]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ B
    · rw [if_pos hi, sum_eq_sum_ite_mem]
      simp [hi]
    · simp [hi]
  have hcount : ∀ i j : Fin n,
      ∑ B ∈ powersetCard m (univ : Finset (Fin n)), (if i ∈ B ∧ j ∈ B then g i j else 0) =
        (if i = j then (n - 1).choose (m - 1) else if 2 ≤ m then (n - 2).choose (m - 2) else 0) •
          g i j := by
    intro i j
    rw [← Finset.sum_filter, Finset.sum_const]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, ← card_powersetCard_mem i hm]
      congr 2
      exact Finset.filter_congr fun B _ => and_self_iff
    · rw [if_neg hij, ← card_powersetCard_pair hij]
  simp_rw [hind]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := powersetCard m univ), hcount]
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_neg (Finset.ne_of_mem_erase hj).symm]

/-! ### Binomial ratios -/

theorem choose_mul_eq_choose_pred {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    m * n.choose m = n * (n - 1).choose (m - 1) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [mul_comm, Nat.add_one_mul_choose_eq]

theorem choose_mul_eq_choose_pred_pred {n m : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    m * (m - 1) * n.choose m = n * (n - 1) * (n - 2).choose (m - 2) := by
  have h1 := choose_mul_eq_choose_pred (by omega : 1 ≤ m) hmn
  have h2 := choose_mul_eq_choose_pred (by omega : 1 ≤ m - 1) (by omega : m - 1 ≤ n - 1)
  rw [show n - 1 - 1 = n - 2 by omega, show m - 1 - 1 = m - 2 by omega] at h2
  calc m * (m - 1) * n.choose m = (m - 1) * (m * n.choose m) := by ring
    _ = (m - 1) * (n * (n - 1).choose (m - 1)) := by rw [h1]
    _ = n * ((m - 1) * (n - 1).choose (m - 1)) := by ring
    _ = n * ((n - 1) * (n - 2).choose (m - 2)) := by rw [h2]
    _ = n * (n - 1) * (n - 2).choose (m - 2) := by ring

/-- The scalar bookkeeping of the finite population correction. -/
theorem fpc_coeff {n m C N₁ N₂ : ℝ} (hn : n ≠ 0) (hn1 : n - 1 ≠ 0) (hm : m ≠ 0) (hC : C ≠ 0)
    (h1 : N₁ * n = C * m) (h2 : N₂ * (n * (n - 1)) = C * (m * (m - 1))) :
    C⁻¹ * ((m⁻¹ * m⁻¹) * (N₁ - N₂)) = (1 - m / n) / (m * (n - 1)) := by
  have hN1 : N₁ = C * m / n := (eq_div_iff hn).mpr h1
  have hN2 : N₂ = C * (m * (m - 1)) / (n * (n - 1)) := (eq_div_iff (mul_ne_zero hn hn1)).mpr h2
  rw [hN1, hN2]
  field_simp
  ring

/-! ### The finite population correction -/

/-- **Cochran's finite population correction, bilinear cross form**: for a uniform `m`-subset `B`
of `n ≥ 2` samples and two families `a b`,
`E_B[β(mean_B a − ā, mean_B b − b̄)] = ((1 − m/n)/(m(n−1))) ∑ᵢ β(aᵢ − ā, bᵢ − b̄)`. -/
theorem fpc_bilinear₂ {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n)
    (β : V →ₗ[ℝ] V →ₗ[ℝ] W) (a b : Fin n → V) :
    (n.choose m : ℝ)⁻¹ • ∑ B ∈ powersetCard m (univ : Finset (Fin n)),
        β (batchMean m a B - popMean a) (batchMean m b B - popMean b) =
      ((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1))) • ∑ i, β (a i - popMean a) (b i - popMean b) := by
  set c : Fin n → V := fun i => a i - popMean a with hc
  set d : Fin n → V := fun i => b i - popMean b with hd
  have hc0 : ∑ i, c i = 0 := sum_sub_popMean (by omega) a
  have hd0 : ∑ i, d i = 0 := sum_sub_popMean (by omega) b
  -- each summand is `(1/m²) ∑_{i,j∈B} β (c i) (d j)`
  have hB : ∀ B ∈ powersetCard m (univ : Finset (Fin n)),
      β (batchMean m a B - popMean a) (batchMean m b B - popMean b) =
        ((m : ℝ)⁻¹ * (m : ℝ)⁻¹) • ∑ i ∈ B, ∑ j ∈ B, β (c i) (d j) := by
    intro B hB
    rw [batchMean_sub_popMean (by omega) a hB, batchMean_sub_popMean (by omega) b hB,
      LinearMap.map_smul₂, map_smul, smul_smul, LinearMap.map_sum₂]
    congr 1
    exact Finset.sum_congr rfl fun i _ => map_sum (β (c i)) _ _
  rw [Finset.sum_congr rfl hB, ← Finset.smul_sum, sum_powersetCard_sum_sum hm]
  -- the off-diagonal sum of centred families is minus the diagonal
  have hoff : ∑ i, ∑ j ∈ univ.erase i, β (c i) (d j) = -∑ i, β (c i) (d i) := by
    have htot : ∑ i, ∑ j, β (c i) (d j) = 0 := by
      have : β (∑ i, c i) (∑ j, d j) = ∑ i, ∑ j, β (c i) (d j) := by
        rw [LinearMap.map_sum₂]
        exact Finset.sum_congr rfl fun i _ => map_sum (β (c i)) _ _
      rw [← this, hc0, hd0]
      simp
    have hsplit : ∑ i, ∑ j, β (c i) (d j) =
        ∑ i, β (c i) (d i) + ∑ i, ∑ j ∈ univ.erase i, β (c i) (d j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    rw [htot] at hsplit
    exact (neg_eq_of_add_eq_zero_right hsplit.symm).symm
  rw [hoff, smul_neg, ← sub_eq_add_neg, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ,
    ← sub_smul, smul_smul, smul_smul]
  congr 1
  -- the scalar identity
  have hC : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmn).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have h1 : ((n - 1).choose (m - 1) : ℝ) * n = (n.choose m : ℝ) * m := by
    have := choose_mul_eq_choose_pred hm hmn
    exact_mod_cast (by rw [mul_comm] at this; linarith [this] :
      (n - 1).choose (m - 1) * n = n.choose m * m)
  have h2 : ((if 2 ≤ m then (n - 2).choose (m - 2) else 0 : ℕ) : ℝ) * (n * ((n : ℝ) - 1)) =
      (n.choose m : ℝ) * (m * ((m : ℝ) - 1)) := by
    split_ifs with h2m
    · have := choose_mul_eq_choose_pred_pred h2m hmn
      have hcast : ((n - 2).choose (m - 2) : ℝ) * (n * ((n : ℝ) - 1)) =
          (n.choose m : ℝ) * (m * ((m : ℝ) - 1)) := by
        have h' : ((n - 2).choose (m - 2) : ℝ) * ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) =
            (n.choose m : ℝ) * ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) := by
          exact_mod_cast (by rw [mul_comm] at this; linarith [this] :
            (n - 2).choose (m - 2) * (n * (n - 1)) = n.choose m * (m * (m - 1)))
        rwa [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h'
      exact hcast
    · have hm1 : m = 1 := by omega
      subst hm1
      simp
  rw [← fpc_coeff hn0 hn1 hm0 hC h1 h2]
  push_cast
  ring

/-- **Cochran's finite population correction, bilinear form**: for a uniform `m`-subset `B` of
`n ≥ 2` samples,
`E_B[β(mean_B a − ā, mean_B a − ā)] = ((1 − m/n)/(m(n−1))) ∑ᵢ β(aᵢ − ā, aᵢ − ā)`. -/
theorem fpc_bilinear {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n)
    (β : V →ₗ[ℝ] V →ₗ[ℝ] W) (a : Fin n → V) :
    (n.choose m : ℝ)⁻¹ • ∑ B ∈ powersetCard m (univ : Finset (Fin n)),
        β (batchMean m a B - popMean a) (batchMean m a B - popMean a) =
      ((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1))) • ∑ i, β (a i - popMean a) (a i - popMean a) :=
  fpc_bilinear₂ hm hmn hn β a a

/-! ### The E8 constants -/

section E8

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The outer product as a bilinear map. -/
noncomputable def outerBilin : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] Matrix ι ι ℝ :=
  LinearMap.mk₂ ℝ vecMulVec (fun x y z => add_vecMulVec x y z)
    (fun c x y => smul_vecMulVec c x y) (fun x y z => vecMulVec_add x y z)
    (fun c x y => vecMulVec_smul c x y)

omit [Fintype ι] [DecidableEq ι] in
/-- The `n − 1` sample covariance of the per-sample gradients. -/
noncomputable def sampleCov {n : ℕ} (g : Fin n → ι → ℝ) : Matrix ι ι ℝ :=
  ((n : ℝ) - 1)⁻¹ • ∑ i, vecMulVec (g i - popMean g) (g i - popMean g)

omit [Fintype ι] [DecidableEq ι] in
/-- **E8, the gradient noise**: the covariance of the minibatch mean gradient about the full
gradient is `C_g = (1/m)(1 − m/n) S²`. -/
theorem minibatch_gradient_cov {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n)
    (g : Fin n → ι → ℝ) :
    (n.choose m : ℝ)⁻¹ • ∑ B ∈ powersetCard m (univ : Finset (Fin n)),
        vecMulVec (batchMean m g B - popMean g) (batchMean m g B - popMean g) =
      ((m : ℝ)⁻¹ * (1 - (m : ℝ) / n)) • sampleCov g := by
  have h := fpc_bilinear hm hmn hn (outerBilin (ι := ι)) g
  simp only [outerBilin, LinearMap.mk₂_apply] at h
  rw [h, sampleCov, smul_smul]
  congr 1
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp

omit [DecidableEq ι] in
/-- The covariance sandwich `(X, Y) ↦ X Σ Yᵀ` as a bilinear map. -/
noncomputable def sandwichBilin (S : Matrix ι ι ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ :=
  LinearMap.mk₂ ℝ (fun X Y => X * S * Yᵀ)
    (fun X X' Y => by simp [add_mul])
    (fun c X Y => by simp)
    (fun X Y Y' => by simp [Matrix.transpose_add, mul_add])
    (fun c X Y => by simp [Matrix.transpose_smul])

set_option linter.unusedDecidableInType false in
/-- **E8, the state-dependent term**: for per-sample Hessians `Hs` with mean `H`,
`E_B[(H_B − H) Σ (H_B − H)ᵀ] = ((1 − m/n)/(m(n−1))) · stateTerm (Hᵢ − H) Σ`, the coefficient of
the full law. -/
theorem minibatch_hessian_term {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hn : 2 ≤ n)
    (Hs : Fin n → Matrix ι ι ℝ) (S : Matrix ι ι ℝ) :
    (n.choose m : ℝ)⁻¹ • ∑ B ∈ powersetCard m (univ : Finset (Fin n)),
        (batchMean m Hs B - popMean Hs) * S * (batchMean m Hs B - popMean Hs)ᵀ =
      ((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1))) • stateTerm (fun i => Hs i - popMean Hs) S := by
  have h := fpc_bilinear hm hmn hn (sandwichBilin S) Hs
  simp only [sandwichBilin, LinearMap.mk₂_apply] at h
  rw [h]
  rfl

/-- The full law's coefficient is `h² t²` times the finite population correction. -/
theorem minibatchCoeff_eq (h t : ℝ) (m n : ℕ) :
    minibatchCoeff h t m n = h ^ 2 * t ^ 2 * ((1 - (m : ℝ) / n) / (m * ((n : ℝ) - 1))) := by
  unfold minibatchCoeff
  ring

end E8

end Laplace.Sampler
