/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.NumeratorTails

/-!
# Asymptotic division

Stage 6 of the forward-expansion programme: the generic finite
division lemma. If `f` and `g` admit order-`N` asymptotic polynomials
at `0⁺` with coefficients `a`, `b` and `b 0 ≠ 0`, then `f/g` admits
the order-`N` asymptotic polynomial with the division coefficients
`c_0 = a_0/b_0`, `c_j = (a_j - ∑_{i=1}^{j} b_i c_{j-i})/b_0`. The
proof telescopes `f - g·C` into the two expansion errors plus the
polynomial `A - B·C`, whose coefficients vanish through degree `N` by
the convolution identity, so it carries `q^{N+1}`; the quotient then
divides by `g`, eventually bounded below by `|b_0|/2`.
-/

open Real Filter Topology Asymptotics Polynomial

namespace Laplace.Multi

/-- The division coefficients, by strong recursion. -/
noncomputable def divisionCoeff (a b : ℕ → ℝ) : ℕ → ℝ
  | j => (a j - ∑ i ∈ (Finset.Icc 1 j).attach,
      b i.1 * divisionCoeff a b (j - i.1)) / b 0
  termination_by j => j
  decreasing_by
    have h1 := (Finset.mem_Icc.mp i.2).1
    have h2 := (Finset.mem_Icc.mp i.2).2
    omega

/-- The recursion, in unattached form. -/
theorem divisionCoeff_eq (a b : ℕ → ℝ) (j : ℕ) :
    divisionCoeff a b j =
      (a j - ∑ i ∈ Finset.Icc 1 j, b i * divisionCoeff a b (j - i)) /
        b 0 := by
  rw [divisionCoeff]
  congr 1
  rw [← Finset.sum_attach (Finset.Icc 1 j)
    (fun i ↦ b i * divisionCoeff a b (j - i))]

private theorem sum_range_shift_eq_sum_Icc' (f : ℕ → ℝ) (N : ℕ) :
    ∑ s ∈ Finset.range N, f (s + 1) = ∑ s ∈ Finset.Icc 1 N, f s := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

/-- **The convolution identity**: the division coefficients invert
the Cauchy product. -/
theorem divisionCoeff_conv (a b : ℕ → ℝ) (hb0 : b 0 ≠ 0) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), b i * divisionCoeff a b (j - i) =
      a j := by
  have h := divisionCoeff_eq a b j
  rw [eq_div_iff hb0] at h
  have hpeel : ∑ i ∈ Finset.range (j + 1),
      b i * divisionCoeff a b (j - i) =
      (∑ i ∈ Finset.Icc 1 j, b i * divisionCoeff a b (j - i)) +
        b 0 * divisionCoeff a b j := by
    rw [Finset.sum_range_succ' (fun i ↦ b i * divisionCoeff a b (j - i)) j]
    rw [sum_range_shift_eq_sum_Icc'
      (fun i ↦ b i * divisionCoeff a b (j - i)) j]
    simp
  rw [hpeel]
  linarith [h]

/-- The coefficient polynomial of a finite coefficient system. -/
noncomputable def coeffPoly (a : ℕ → ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (N + 1), Polynomial.C (a j) * Polynomial.X ^ j

theorem coeffPoly_eval (a : ℕ → ℝ) (N : ℕ) (q : ℝ) :
    (coeffPoly a N).eval q =
      ∑ j ∈ Finset.range (N + 1), a j * q ^ j := by
  unfold coeffPoly
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]

theorem coeffPoly_coeff (a : ℕ → ℝ) (N m : ℕ) :
    (coeffPoly a N).coeff m =
      if m ∈ Finset.range (N + 1) then a m else 0 := by
  unfold coeffPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite,
    mul_one, mul_zero]
  exact Finset.sum_ite_eq _ m a

theorem natDegree_coeffPoly_le (a : ℕ → ℝ) (N : ℕ) :
    (coeffPoly a N).natDegree ≤ N := by
  unfold coeffPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_
  calc (Polynomial.C (a j) * Polynomial.X ^ j).natDegree
      ≤ (Polynomial.X ^ j : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
    _ = j := Polynomial.natDegree_X_pow j
    _ ≤ N := by
        have := Finset.mem_range.mp hj
        omega

/-- The Cauchy product of the polynomials realizes the convolution
through degree `N`. -/
theorem coeffPoly_mul_coeff (b c : ℕ → ℝ) (N : ℕ) {m : ℕ}
    (hm : m ≤ N) :
    (coeffPoly b N * coeffPoly c N).coeff m =
      ∑ i ∈ Finset.range (m + 1), b i * c (m - i) := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hiN : i ≤ N := by
    have := Finset.mem_range.mp hi
    omega
  have hmiN : m - i ≤ N := by omega
  rw [coeffPoly_coeff, coeffPoly_coeff,
    if_pos (Finset.mem_range.mpr (by omega)),
    if_pos (Finset.mem_range.mpr (by omega))]

/-- The tail bound for a polynomial with vanishing low coefficients. -/
theorem poly_vanishing_tail_bound {p : Polynomial ℝ} {N : ℕ}
    (hcoeff : ∀ m ≤ N, p.coeff m = 0) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    |p.eval q| ≤ q ^ (N + 1) *
      ∑ m ∈ Finset.Ico (N + 1) (max (p.natDegree + 1) (N + 1)),
        |p.coeff m| := by
  have hdeg : p.natDegree < max (p.natDegree + 1) (N + 1) :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hNn : N + 1 ≤ max (p.natDegree + 1) (N + 1) := le_max_right _ _
  rw [Polynomial.eval_eq_sum_range' hdeg]
  have hsplit : ∑ m ∈ Finset.range (max (p.natDegree + 1) (N + 1)),
      p.coeff m * q ^ m =
      (∑ m ∈ Finset.range (N + 1), p.coeff m * q ^ m) +
        ∑ m ∈ Finset.Ico (N + 1) (max (p.natDegree + 1) (N + 1)),
          p.coeff m * q ^ m := by
    simp only [Finset.range_eq_Ico]
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) hNn]
  have hlow : ∑ m ∈ Finset.range (N + 1), p.coeff m * q ^ m = 0 :=
    Finset.sum_eq_zero fun m hm ↦ by
      rw [hcoeff m (by
        have := Finset.mem_range.mp hm
        omega), zero_mul]
  rw [hsplit, hlow, zero_add]
  calc |∑ m ∈ Finset.Ico (N + 1) (max (p.natDegree + 1) (N + 1)),
        p.coeff m * q ^ m|
      ≤ ∑ m ∈ Finset.Ico (N + 1) (max (p.natDegree + 1) (N + 1)),
          |p.coeff m * q ^ m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Ico (N + 1) (max (p.natDegree + 1) (N + 1)),
          |p.coeff m| * q ^ (N + 1) := by
        refine Finset.sum_le_sum fun m hm ↦ ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 m)]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hq0 hq1 (Finset.mem_Ico.mp hm).1)
          (abs_nonneg _)
    _ = q ^ (N + 1) *
          ∑ m ∈ Finset.Ico (N + 1) (max (p.natDegree + 1) (N + 1)),
            |p.coeff m| := by
        rw [← Finset.sum_mul]
        ring

/-- **Asymptotic division**: the quotient of order-`N` expansions,
when the denominator's constant coefficient is nonzero, admits the
order-`N` expansion with the division coefficients. -/
theorem isAsymptoticExpansionTo_div {f g : ℝ → ℝ} {a b : ℕ → ℝ}
    {N : ℕ}
    (hf : Laplace.IsAsymptoticExpansionTo f a N)
    (hg : Laplace.IsAsymptoticExpansionTo g b N) (hb0 : b 0 ≠ 0) :
    Laplace.IsAsymptoticExpansionTo (fun q : ℝ ↦ f q / g q)
      (divisionCoeff a b) N := by
  set c : ℕ → ℝ := divisionCoeff a b with hc_def
  unfold Laplace.IsAsymptoticExpansionTo at hf hg ⊢
  have hb0' : (0 : ℝ) < |b 0| := abs_pos.mpr hb0
  -- the coefficient polynomial functions are bounded near 0⁺
  have hClim : Tendsto (fun q : ℝ ↦
      ∑ j ∈ Finset.range (N + 1), c j * q ^ j) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ j ∈ Finset.range (N + 1), c j * (0 : ℝ) ^ j)) := by
    have hcont : Continuous fun q : ℝ ↦
        ∑ j ∈ Finset.range (N + 1), c j * q ^ j :=
      continuous_finset_sum _ fun j _ ↦
        continuous_const.mul (continuous_pow j)
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hCbig : (fun q : ℝ ↦
      ∑ j ∈ Finset.range (N + 1), c j * q ^ j)
      =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hClim.isBigO_one ℝ
  -- g tends to b 0 and is eventually bounded below
  have hBlim : Tendsto (fun q : ℝ ↦
      ∑ j ∈ Finset.range (N + 1), b j * q ^ j) (𝓝[>] (0 : ℝ))
      (𝓝 (b 0)) := by
    have hcont : Continuous fun q : ℝ ↦
        ∑ j ∈ Finset.range (N + 1), b j * q ^ j :=
      continuous_finset_sum _ fun j _ ↦
        continuous_const.mul (continuous_pow j)
    have h0 : ∑ j ∈ Finset.range (N + 1), b j * (0 : ℝ) ^ j = b 0 := by
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro j _ hj
        rw [zero_pow hj, mul_zero]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    have h2 : Tendsto (fun q : ℝ ↦
        ∑ j ∈ Finset.range (N + 1), b j * q ^ j) (𝓝[>] (0 : ℝ))
        (𝓝 (∑ j ∈ Finset.range (N + 1), b j * (0 : ℝ) ^ j)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    rwa [h0] at h2
  have hqN1 : (fun q : ℝ ↦ q ^ N) =O[𝓝[>] (0 : ℝ)]
      (fun _ : ℝ ↦ (1 : ℝ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)]
      with q hq
    obtain ⟨hq0, hq1⟩ := hq
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, mul_one,
      abs_of_pos (pow_pos hq0 N)]
    exact pow_le_one₀ hq0.le hq1.le
  have hgerr : Tendsto (fun q : ℝ ↦
      g q - ∑ j ∈ Finset.range (N + 1), b j * q ^ j)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (isLittleO_one_iff ℝ).mp (hg.trans_isBigO hqN1)
  have hglim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (b 0)) := by
    have hsum := hgerr.add hBlim
    rw [zero_add] at hsum
    refine hsum.congr fun q ↦ ?_
    ring
  have hglow : ∀ᶠ q in 𝓝[>] (0 : ℝ), |b 0| / 2 ≤ |g q| := by
    have habs : Tendsto (fun q : ℝ ↦ |g q|) (𝓝[>] (0 : ℝ))
        (𝓝 |b 0|) := hglim.abs
    exact habs.eventually_const_le (half_lt_self hb0')
  -- the polynomial difference vanishes through degree N
  set pdiff : Polynomial ℝ := coeffPoly a N - coeffPoly b N * coeffPoly c N
    with hp_def
  have hpcoeff : ∀ m ≤ N, pdiff.coeff m = 0 := by
    intro m hm
    rw [hp_def, Polynomial.coeff_sub, coeffPoly_coeff,
      if_pos (Finset.mem_range.mpr (by omega)),
      coeffPoly_mul_coeff b c N hm, divisionCoeff_conv a b hb0 m,
      sub_self]
  have hpoly : (fun q : ℝ ↦
      (∑ j ∈ Finset.range (N + 1), a j * q ^ j) -
        (∑ j ∈ Finset.range (N + 1), b j * q ^ j) *
          ∑ j ∈ Finset.range (N + 1), c j * q ^ j)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N := by
    have hbig : (fun q : ℝ ↦
        (∑ j ∈ Finset.range (N + 1), a j * q ^ j) -
          (∑ j ∈ Finset.range (N + 1), b j * q ^ j) *
            ∑ j ∈ Finset.range (N + 1), c j * q ^ j)
        =O[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ (N + 1) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨∑ m ∈ Finset.Ico (N + 1)
        (max (pdiff.natDegree + 1) (N + 1)), |pdiff.coeff m|, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)]
        with q hq
      obtain ⟨hq0, hq1⟩ := hq
      have heval : pdiff.eval q =
          (∑ j ∈ Finset.range (N + 1), a j * q ^ j) -
            (∑ j ∈ Finset.range (N + 1), b j * q ^ j) *
              ∑ j ∈ Finset.range (N + 1), c j * q ^ j := by
        rw [hp_def, Polynomial.eval_sub, Polynomial.eval_mul,
          coeffPoly_eval, coeffPoly_eval, coeffPoly_eval]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, ← heval,
        abs_of_pos (pow_pos hq0 (N + 1)), mul_comm]
      exact poly_vanishing_tail_bound hpcoeff hq0.le hq1.le
    exact hbig.trans_isLittleO (isLittleO_pow_succ_nhdsGT N)
  -- the numerator estimate
  have hnum : (fun q : ℝ ↦
      f q - g q * ∑ j ∈ Finset.range (N + 1), c j * q ^ j)
      =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N := by
    have h2 : (fun q : ℝ ↦
        (g q - ∑ j ∈ Finset.range (N + 1), b j * q ^ j) *
          ∑ j ∈ Finset.range (N + 1), c j * q ^ j)
        =o[𝓝[>] (0 : ℝ)] fun q : ℝ ↦ q ^ N := by
      have := hg.mul_isBigO hCbig
      refine this.congr' (Filter.EventuallyEq.refl _ _) ?_
      filter_upwards with q
      rw [mul_one]
    have hcomb := (hf.sub h2).add hpoly
    refine hcomb.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards with q
    ring
  -- assemble the quotient
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  rw [Asymptotics.isLittleO_iff] at hnum
  have hnum' := hnum (show (0 : ℝ) < ε * (|b 0| / 2) by positivity)
  filter_upwards [hnum', hglow, self_mem_nhdsWithin]
    with q h1 h2 hq0'
  have hq0 : (0 : ℝ) < q := hq0'
  have hgne : g q ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at h2
    linarith
  have hquot : f q / g q -
      ∑ j ∈ Finset.range (N + 1), c j * q ^ j =
      (f q - g q * ∑ j ∈ Finset.range (N + 1), c j * q ^ j) / g q := by
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h1 ⊢
  rw [hquot, abs_div]
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) h2)]
  calc |f q - g q * ∑ j ∈ Finset.range (N + 1), c j * q ^ j|
      ≤ ε * (|b 0| / 2) * |q ^ N| := h1
    _ = ε * |q ^ N| * (|b 0| / 2) := by ring
    _ ≤ ε * |q ^ N| * |g q| :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

end Laplace.Multi
