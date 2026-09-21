/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Cyclic blindness: no finite family of polynomial rescaled tests identifies germs in `d = 2`

The fixed-rescaled-test identifiability question, closed negatively for polynomial tests. On
`ℂ ≅ ℝ²` consider, for `N ≥ 3` and `ε ≠ 0`, the one-parameter family of analytic losses
`L_θ(z) = ½|z|² + ε Re(e^{-iNθ} z^N) + ε² |z|^{2N-2}` (`cycLoss`). Every `L_θ` has a unique zero
at `0`, the global lower bound `L_θ ≥ ¼|z|²` (`cycLoss_lower`), the same quadratic part `½|z|²`
(`cycLoss_sub_quadratic_le`), and the germs at `0` differ as soon as `e^{-iNθ} ≠ e^{-iNθ'}`
(`cycLoss_germs_differ`). Yet for every polynomial `P` of degree `< N` in the real coordinates,
every radial cutoff `χ(|z|)` and every temperature `t`, the expectation `∫ P χ e^{-tL_θ}` is
independent of `θ` (`cycExp_eq_of_mem_lowSpanLe`), EXACTLY in `t`, and so is the normalised
expectation of the rescaled test `P(√t ·)` (`normalized_rescaled_eq`). Mechanism:
`L_θ(z) = L_0(e^{-iθ}z)`, so rotating the variable gives
`E_θ[z^p z̄^q] = e^{i(p-q)θ} E_0[z^p z̄^q]`; and `L_0` is invariant under `z ↦ ωz`, `ω = e^{2πi/N}`,
so `E_0[z^p z̄^q] = ω^{p-q} E_0[z^p z̄^q]`,
which forces `E_0[z^p z̄^q] = 0` unless `p ≡ q (mod N)`; with `p + q < N` that means `p = q`, where
the rotation factor is `1`. Real monomials `x^p y^q` are combinations of the `z^a z̄^b` with
`a + b = p + q` (`re_im_pow_mem_lowSpanLe`).

Consequence (`finite_polynomial_tests_blind`): for every degree bound `m` there is a family
of analytic losses with common nondegenerate quadratic part and pairwise distinct germs that
no polynomial rescaled test of degree `≤ m` can tell apart at any temperature. Contrast the
one-dimensional case, where the two tests `u, u²` recover the Taylor series triangularly.
(Astra consult `gpt_responses/research_morse_bott_normal_form_v1.md`, Q3.)
-/

open Complex MeasureTheory Real
open ComplexConjugate

namespace Laplace.Multi.Cyclic

/-! ### The loss family -/

/-- `L_θ(z) = ½|z|² + ε Re(e^{-iNθ} z^N) + ε² |z|^{2N-2}`. -/
noncomputable def cycLoss (N : ℕ) (ε θ : ℝ) (z : ℂ) : ℝ :=
  ‖z‖ ^ 2 / 2 + ε * (Complex.exp (-((N : ℝ) * θ : ℝ) * I) * z ^ N).re + ε ^ 2 * ‖z‖ ^ (2 * N - 2)

/-- The primitive `N`-th root of unity `ω = e^{2πi/N}`. -/
noncomputable def omega (N : ℕ) : ℂ := Complex.exp (((2 * π / N : ℝ)) * I)

theorem norm_omega (N : ℕ) : ‖omega N‖ = 1 := norm_exp_ofReal_mul_I _

theorem omega_pow (N : ℕ) (hN : N ≠ 0) : omega N ^ N = 1 := by
  unfold omega
  rw [← Complex.exp_nat_mul]
  have : (N : ℂ) * (((2 * π / N : ℝ) : ℂ) * I) = 2 * π * I := by
    push_cast
    field_simp
  rw [this, Complex.exp_two_pi_mul_I]

theorem norm_exp_neg_ofReal_mul_I (x : ℝ) : ‖Complex.exp (-(x : ℂ) * I)‖ = 1 := by
  have := norm_exp_ofReal_mul_I (-x)
  rwa [Complex.ofReal_neg] at this

/-- `L_θ` is invariant under the cyclic rotation `z ↦ ωz`. -/
theorem cycLoss_omega_mul (N : ℕ) (hN : N ≠ 0) (ε θ : ℝ) (z : ℂ) :
    cycLoss N ε θ (omega N * z) = cycLoss N ε θ z := by
  unfold cycLoss
  rw [norm_mul, norm_omega, one_mul, mul_pow, omega_pow N hN, one_mul]

/-- `L_θ(z) = L_0(e^{-iθ} z)`. -/
theorem cycLoss_eq_rot (N : ℕ) (ε θ : ℝ) (z : ℂ) :
    cycLoss N ε θ z = cycLoss N ε 0 (Complex.exp (-(θ : ℂ) * I) * z) := by
  unfold cycLoss
  rw [norm_mul, norm_exp_neg_ofReal_mul_I, one_mul, mul_pow, ← Complex.exp_nat_mul]
  congr 3
  simp only [mul_zero, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul]
  congr 1
  push_cast
  ring_nf

theorem abs_re_mul_pow_le (c z : ℂ) (hc : ‖c‖ = 1) (N : ℕ) : |(c * z ^ N).re| ≤ ‖z‖ ^ N := by
  calc |(c * z ^ N).re| ≤ ‖c * z ^ N‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ ^ N := by rw [norm_mul, hc, one_mul, norm_pow]

/-- **Global quadratic lower bound**: `L_θ ≥ ¼ |z|²`; in particular `0` is the unique zero and
it is nondegenerate. -/
theorem cycLoss_lower (N : ℕ) (hN : 2 ≤ N) (ε θ : ℝ) (z : ℂ) :
    ‖z‖ ^ 2 / 4 ≤ cycLoss N ε θ z := by
  unfold cycLoss
  set s : ℝ := ε * ‖z‖ ^ (N - 2) with hs
  have hN' : ‖z‖ ^ N = ‖z‖ ^ (N - 2) * ‖z‖ ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have h2N : ‖z‖ ^ (2 * N - 2) = (‖z‖ ^ (N - 2)) ^ 2 * ‖z‖ ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hre := abs_re_mul_pow_le (Complex.exp (-((N : ℝ) * θ : ℝ) * I)) z
    (norm_exp_neg_ofReal_mul_I _) N
  have hbound : -(|s| * ‖z‖ ^ 2) ≤ ε * (Complex.exp (-((N : ℝ) * θ : ℝ) * I) * z ^ N).re := by
    have h1 : |ε * (Complex.exp (-((N : ℝ) * θ : ℝ) * I) * z ^ N).re| ≤ |s| * ‖z‖ ^ 2 := by
      rw [abs_mul, hs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖z‖ ^ (N - 2)), mul_assoc,
        ← hN']
      exact mul_le_mul_of_nonneg_left hre (abs_nonneg _)
    linarith [neg_abs_le (ε * (Complex.exp (-((N : ℝ) * θ : ℝ) * I) * z ^ N).re)]
  have hq : ε ^ 2 * ‖z‖ ^ (2 * N - 2) = s ^ 2 * ‖z‖ ^ 2 := by
    rw [h2N, hs]
    ring
  rw [hq]
  have hsq : 0 ≤ (|s| - 1 / 2) ^ 2 := sq_nonneg _
  have hs2 : |s| ^ 2 = s ^ 2 := sq_abs s
  nlinarith [norm_nonneg z, sq_nonneg ‖z‖, mul_nonneg (sq_nonneg ‖z‖) hsq]

/-- **Common quadratic part**: `|L_θ(z) - ½|z|²| ≤ (|ε| + ε² |z|^{N-2}) |z|^N`. -/
theorem cycLoss_sub_quadratic_le (N : ℕ) (hN : 2 ≤ N) (ε θ : ℝ) (z : ℂ) :
    |cycLoss N ε θ z - ‖z‖ ^ 2 / 2| ≤ (|ε| + ε ^ 2 * ‖z‖ ^ (N - 2)) * ‖z‖ ^ N := by
  unfold cycLoss
  have h2N : ‖z‖ ^ (2 * N - 2) = ‖z‖ ^ (N - 2) * ‖z‖ ^ N := by
    rw [← pow_add]
    congr 1
    omega
  have hre := abs_re_mul_pow_le (Complex.exp (-((N : ℝ) * θ : ℝ) * I)) z
    (norm_exp_neg_ofReal_mul_I _) N
  rw [show ‖z‖ ^ 2 / 2 + ε * (Complex.exp (-((N : ℝ) * θ : ℝ) * I) * z ^ N).re +
      ε ^ 2 * ‖z‖ ^ (2 * N - 2) - ‖z‖ ^ 2 / 2 =
      ε * (Complex.exp (-((N : ℝ) * θ : ℝ) * I) * z ^ N).re + ε ^ 2 * ‖z‖ ^ (2 * N - 2) by ring]
  calc |ε * (Complex.exp (-((N : ℝ) * θ : ℝ) * I) * z ^ N).re + ε ^ 2 * ‖z‖ ^ (2 * N - 2)|
      ≤ |ε * (Complex.exp (-((N : ℝ) * θ : ℝ) * I) * z ^ N).re| + |ε ^ 2 * ‖z‖ ^ (2 * N - 2)| :=
        abs_add_le _ _
    _ ≤ |ε| * ‖z‖ ^ N + ε ^ 2 * ‖z‖ ^ (N - 2) * ‖z‖ ^ N := by
        gcongr
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hre (abs_nonneg _)
        · rw [abs_of_nonneg (by positivity), h2N]
          ring_nf
          exact le_rfl
    _ = (|ε| + ε ^ 2 * ‖z‖ ^ (N - 2)) * ‖z‖ ^ N := by ring

/-- **The germs differ**: if `ε ≠ 0` and `e^{-iNθ} ≠ e^{-iNθ'}`, then `L_θ ≠ L_θ'` at points
arbitrarily close to `0`. -/
theorem cycLoss_germs_differ (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : ε ≠ 0) {θ θ' : ℝ}
    (h : Complex.exp (-((N : ℝ) * θ : ℝ) * I) ≠ Complex.exp (-((N : ℝ) * θ' : ℝ) * I)) :
    ∀ δ > 0, ∃ z : ℂ, ‖z‖ < δ ∧ cycLoss N ε θ z ≠ cycLoss N ε θ' z := by
  intro δ hδ
  set e := Complex.exp (-((N : ℝ) * θ : ℝ) * I) with he
  set e' := Complex.exp (-((N : ℝ) * θ' : ℝ) * I) with he'
  have hne : e - e' ≠ 0 := sub_ne_zero.mpr h
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (conj (e - e')) hN
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hw
    have h0 : conj (e - e') = 0 := hw.symm
    have h1 := congrArg conj h0
    rw [Complex.conj_conj, map_zero] at h1
    exact hne h1
  set ρ : ℝ := δ / (2 * (‖w‖ + 1)) with hρ
  have hρpos : 0 < ρ := by positivity
  refine ⟨(ρ : ℂ) * w, ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos, hρ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  · intro heq
    have hdiff : cycLoss N ε θ ((ρ : ℂ) * w) - cycLoss N ε θ' ((ρ : ℂ) * w) =
        ε * ((e - e') * ((ρ : ℂ) * w) ^ N).re := by
      unfold cycLoss
      rw [← he, ← he']
      rw [sub_mul, Complex.sub_re]
      ring
    rw [heq, sub_self] at hdiff
    have hval : ((e - e') * ((ρ : ℂ) * w) ^ N).re = ρ ^ N * Complex.normSq (e - e') := by
      have : (e - e') * ((ρ : ℂ) * w) ^ N = ((ρ ^ N * Complex.normSq (e - e') : ℝ) : ℂ) := by
        rw [mul_pow, show (e - e') * ((ρ : ℂ) ^ N * w ^ N) = (ρ : ℂ) ^ N * ((e - e') * w ^ N) by
          ring, hw, Complex.mul_conj]
        push_cast
        ring
      rw [this, Complex.ofReal_re]
    rw [hval] at hdiff
    have hnsq : 0 < Complex.normSq (e - e') := Complex.normSq_pos.mpr hne
    have : ε * (ρ ^ N * Complex.normSq (e - e')) ≠ 0 := by positivity
    exact this hdiff.symm

/-! ### Rotation invariance of Lebesgue measure on `ℂ` -/

theorem measurePreserving_rotation (a : Circle) :
    MeasurePreserving (rotation a) (volume : Measure ℂ) volume := by
  refine ⟨(rotation a).continuous.measurable, ?_⟩
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ℂ))
    (f := ((rotation a).toLinearEquiv : ℂ →ₗ[ℝ] ℂ)) (by rw [det_rotation]; exact one_ne_zero)
  rw [det_rotation, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  exact h

theorem integral_comp_rotation (a : Circle) (g : ℂ → ℂ) : ∫ z, g (a * z) = ∫ z, g z := by
  have h := (measurePreserving_rotation a).integral_comp
    (rotation a).toHomeomorph.measurableEmbedding g
  simpa [rotation_apply] using h

theorem integral_comp_exp_mul (θ : ℝ) (g : ℂ → ℂ) :
    ∫ z, g (Complex.exp ((θ : ℂ) * I) * z) = ∫ z, g z := by
  have := integral_comp_rotation (Circle.exp θ) g
  simpa [Circle.coe_exp] using this

theorem omega_eq_circle (N : ℕ) : omega N = (Circle.exp (2 * π / N) : ℂ) := by
  rw [Circle.coe_exp]
  rfl

theorem integral_comp_omega_mul (N : ℕ) (g : ℂ → ℂ) : ∫ z, g (omega N * z) = ∫ z, g z := by
  rw [omega_eq_circle]
  exact integral_comp_rotation _ g

/-! ### Expectations and the mode-killing argument -/

/-- The weight `χ(|z|) e^{-tL_θ(z)}`, as a complex number. -/
noncomputable def cycWeight (N : ℕ) (ε : ℝ) (χ : ℝ → ℝ) (t θ : ℝ) (z : ℂ) : ℂ :=
  ((χ ‖z‖ * Real.exp (-(t * cycLoss N ε θ z)) : ℝ) : ℂ)

/-- The (unnormalised, complex-valued) expectation `∫ f χ(|z|) e^{-tL_θ}`. -/
noncomputable def cycExp (N : ℕ) (ε : ℝ) (χ : ℝ → ℝ) (t θ : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ z, f z * cycWeight N ε χ t θ z

theorem cycWeight_rot (N : ℕ) (ε : ℝ) (χ : ℝ → ℝ) (t θ : ℝ) (z : ℂ) :
    cycWeight N ε χ t θ (Complex.exp ((θ : ℂ) * I) * z) = cycWeight N ε χ t 0 z := by
  unfold cycWeight
  rw [cycLoss_eq_rot N ε θ, norm_mul, norm_exp_ofReal_mul_I, one_mul, ← mul_assoc,
    ← Complex.exp_add]
  congr 3
  rw [show -(θ : ℂ) * I + (θ : ℂ) * I = 0 by ring, Complex.exp_zero, one_mul]

theorem cycWeight_omega (N : ℕ) (hN : N ≠ 0) (ε : ℝ) (χ : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    cycWeight N ε χ t 0 (omega N * z) = cycWeight N ε χ t 0 z := by
  unfold cycWeight
  rw [cycLoss_omega_mul N hN, norm_mul, norm_omega, one_mul]

/-- Rotating the variable: `E_θ[f] = E_0[f(e^{iθ} ·)]`. -/
theorem cexp_eq_rot (N : ℕ) (ε : ℝ) (χ : ℝ → ℝ) (t θ : ℝ) (f : ℂ → ℂ) :
    cycExp N ε χ t θ f = cycExp N ε χ t 0 fun z ↦ f (Complex.exp ((θ : ℂ) * I) * z) := by
  unfold cycExp
  rw [← integral_comp_exp_mul θ (fun z ↦ f z * cycWeight N ε χ t θ z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only
  rw [cycWeight_rot]

/-- Cyclic invariance at `θ = 0`: `E_0[f] = E_0[f(ω ·)]`. -/
theorem cexp_zero_eq_omega (N : ℕ) (hN : N ≠ 0) (ε : ℝ) (χ : ℝ → ℝ) (t : ℝ) (f : ℂ → ℂ) :
    cycExp N ε χ t 0 f = cycExp N ε χ t 0 fun z ↦ f (omega N * z) := by
  unfold cycExp
  rw [← integral_comp_omega_mul N (fun z ↦ f z * cycWeight N ε χ t 0 z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only
  rw [cycWeight_omega N hN]

/-- The complex monomial `z^p z̄^q`. -/
noncomputable def cmon (p q : ℕ) (z : ℂ) : ℂ := z ^ p * conj z ^ q

theorem cmon_mul_left (p q : ℕ) (a z : ℂ) : cmon p q (a * z) = a ^ p * conj a ^ q * cmon p q z := by
  unfold cmon
  rw [mul_pow, map_mul, mul_pow]
  ring

theorem cexp_cmon_rot (N : ℕ) (ε : ℝ) (χ : ℝ → ℝ) (t θ : ℝ) (p q : ℕ) :
    cycExp N ε χ t θ (cmon p q) =
      Complex.exp ((θ : ℂ) * I) ^ p * conj (Complex.exp ((θ : ℂ) * I)) ^ q *
        cycExp N ε χ t 0 (cmon p q) := by
  rw [cexp_eq_rot]
  unfold cycExp
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only
  rw [cmon_mul_left]
  ring

theorem cexp_cmon_omega (N : ℕ) (hN : N ≠ 0) (ε : ℝ) (χ : ℝ → ℝ) (t : ℝ) (p q : ℕ) :
    cycExp N ε χ t 0 (cmon p q) =
      omega N ^ p * conj (omega N) ^ q * cycExp N ε χ t 0 (cmon p q) := by
  conv_lhs => rw [cexp_zero_eq_omega N hN]
  unfold cycExp
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only
  rw [cmon_mul_left]
  ring

theorem conj_omega (N : ℕ) : conj (omega N) = Complex.exp (-((2 * π / N : ℝ) : ℂ) * I) := by
  unfold omega
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem omega_mul_conj (N : ℕ) : omega N * conj (omega N) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_omega]
  simp

/-- `ω^p ω̄^q ≠ 1` when `p ≠ q` and `p + q < N`. -/
theorem omega_pow_mul_conj_pow_ne_one (N : ℕ) (hN : N ≠ 0) {p q : ℕ} (hpq : p ≠ q)
    (hlt : p + q < N) : omega N ^ p * conj (omega N) ^ q ≠ 1 := by
  have key : ∀ k : ℕ, 0 < k → k < N → omega N ^ k ≠ 1 := by
    intro k hk hkN
    unfold omega
    rw [← Complex.exp_nat_mul]
    intro h1
    have h2 : Complex.exp (2 * π * I * k / N) = 1 := by
      rw [← h1]
      congr 1
      push_cast
      field_simp
    have hdvd := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hN).mp h2
    exact absurd (Nat.le_of_dvd hk hdvd) (by omega)
  have hunit : omega N * conj (omega N) = 1 := omega_mul_conj N
  rcases Nat.lt_or_gt_of_ne hpq with hlt' | hgt
  · -- `p < q`: the product is `ω̄^{q-p}`
    obtain ⟨k, rfl⟩ : ∃ k, q = p + k := ⟨q - p, by omega⟩
    have hk : 0 < k := by omega
    rw [pow_add, show omega N ^ p * (conj (omega N) ^ p * conj (omega N) ^ k) =
      (omega N * conj (omega N)) ^ p * conj (omega N) ^ k by ring, hunit, one_pow, one_mul]
    intro h1
    apply key k hk (by omega)
    have h2 : conj (omega N ^ k) = 1 := by rw [map_pow, h1]
    have h3 := congrArg conj h2
    rwa [Complex.conj_conj, map_one] at h3
  · obtain ⟨k, rfl⟩ : ∃ k, p = q + k := ⟨p - q, by omega⟩
    have hk : 0 < k := by omega
    rw [pow_add, show omega N ^ q * omega N ^ k * conj (omega N) ^ q =
      (omega N * conj (omega N)) ^ q * omega N ^ k by ring, hunit, one_pow, one_mul]
    exact key k hk (by omega)

/-- **Mode killing**: for `p ≠ q` with `p + q < N`, `E_0[z^p z̄^q] = 0`. -/
theorem cexp_cmon_zero_of_ne (N : ℕ) (hN : N ≠ 0) (ε : ℝ) (χ : ℝ → ℝ) (t : ℝ) {p q : ℕ}
    (hpq : p ≠ q) (hlt : p + q < N) : cycExp N ε χ t 0 (cmon p q) = 0 := by
  have h := cexp_cmon_omega N hN ε χ t p q
  have hc := omega_pow_mul_conj_pow_ne_one N hN hpq hlt
  have : (1 - omega N ^ p * conj (omega N) ^ q) * cycExp N ε χ t 0 (cmon p q) = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hc
  · exact h0

theorem exp_pow_mul_conj_pow_self (θ : ℝ) (p : ℕ) :
    Complex.exp ((θ : ℂ) * I) ^ p * conj (Complex.exp ((θ : ℂ) * I)) ^ p = 1 := by
  rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_exp_ofReal_mul_I]
  simp

/-- **Every complex monomial of degree `< N` has a `θ`-independent expectation.** -/
theorem cexp_cmon_eq (N : ℕ) (hN : N ≠ 0) (ε : ℝ) (χ : ℝ → ℝ) (t θ : ℝ) {p q : ℕ}
    (hlt : p + q < N) : cycExp N ε χ t θ (cmon p q) = cycExp N ε χ t 0 (cmon p q) := by
  rw [cexp_cmon_rot]
  by_cases hpq : p = q
  · subst hpq
    rw [exp_pow_mul_conj_pow_self, one_mul]
  · rw [cexp_cmon_zero_of_ne N hN ε χ t hpq hlt, mul_zero]

/-! ### Polynomials of bounded degree -/

/-- The polynomials of degree `≤ d`: the `ℂ`-span of the monomials `z^p z̄^q`, `p + q ≤ d`. -/
noncomputable def lowSpanLe (d : ℕ) : Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ {f | ∃ p q : ℕ, p + q ≤ d ∧ f = cmon p q}

theorem cmon_mem_lowSpanLe {p q d : ℕ} (h : p + q ≤ d) : cmon p q ∈ lowSpanLe d :=
  Submodule.subset_span ⟨p, q, h, rfl⟩

theorem lowSpanLe_mono {d d' : ℕ} (h : d ≤ d') : lowSpanLe d ≤ lowSpanLe d' :=
  Submodule.span_mono fun _ ⟨p, q, hpq, hf⟩ ↦ ⟨p, q, hpq.trans h, hf⟩

theorem cmon_mul_cmon (p q p' q' : ℕ) : cmon p q * cmon p' q' = cmon (p + p') (q + q') := by
  funext z
  simp only [Pi.mul_apply, cmon, pow_add]
  ring

theorem lowSpanLe_mul {a b : ℕ} {f g : ℂ → ℂ} (hf : f ∈ lowSpanLe a) (hg : g ∈ lowSpanLe b) :
    f * g ∈ lowSpanLe (a + b) := by
  have h := Submodule.mul_mem_mul hf hg
  rw [lowSpanLe, lowSpanLe, Submodule.span_mul_span] at h
  refine (Submodule.span_le.mpr ?_) h
  rintro _ ⟨u, ⟨p, q, hpq, rfl⟩, v, ⟨p', q', hpq', rfl⟩, rfl⟩
  change cmon p q * cmon p' q' ∈ (lowSpanLe (a + b) : Set (ℂ → ℂ))
  rw [cmon_mul_cmon]
  exact cmon_mem_lowSpanLe (by omega)

theorem lowSpanLe_pow {a : ℕ} {f : ℂ → ℂ} (hf : f ∈ lowSpanLe a) :
    ∀ k : ℕ, f ^ k ∈ lowSpanLe (k * a)
  | 0 => by
    simp only [pow_zero, zero_mul]
    have : (1 : ℂ → ℂ) = cmon 0 0 := by
      funext z
      simp [cmon]
    rw [this]
    exact cmon_mem_lowSpanLe le_rfl
  | k + 1 => by
    rw [pow_succ, show (k + 1) * a = k * a + a by ring]
    exact lowSpanLe_mul (lowSpanLe_pow hf k) hf

theorem re_mem_lowSpanLe : (fun z : ℂ ↦ (z.re : ℂ)) ∈ lowSpanLe 1 := by
  have h : (fun z : ℂ ↦ (z.re : ℂ)) = (1 / 2 : ℂ) • cmon 1 0 + (1 / 2 : ℂ) • cmon 0 1 := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, cmon, pow_one, pow_zero, mul_one, one_mul,
      smul_eq_mul]
    rw [Complex.re_eq_add_conj]
    ring
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (cmon_mem_lowSpanLe le_rfl))
    (Submodule.smul_mem _ _ (cmon_mem_lowSpanLe le_rfl))

theorem im_mem_lowSpanLe : (fun z : ℂ ↦ (z.im : ℂ)) ∈ lowSpanLe 1 := by
  have h : (fun z : ℂ ↦ (z.im : ℂ)) =
      (1 / (2 * I) : ℂ) • cmon 1 0 + (-(1 / (2 * I)) : ℂ) • cmon 0 1 := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, cmon, pow_one, pow_zero, mul_one, one_mul,
      smul_eq_mul]
    rw [Complex.im_eq_sub_conj]
    ring
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (cmon_mem_lowSpanLe le_rfl))
    (Submodule.smul_mem _ _ (cmon_mem_lowSpanLe le_rfl))

/-- **Real monomials** `x^p y^q` are polynomials of degree `p + q`. -/
theorem re_im_pow_mem_lowSpanLe (p q : ℕ) :
    (fun z : ℂ ↦ (z.re : ℂ) ^ p * (z.im : ℂ) ^ q) ∈ lowSpanLe (p + q) := by
  have h1 := lowSpanLe_pow re_mem_lowSpanLe p
  have h2 := lowSpanLe_pow im_mem_lowSpanLe q
  rw [mul_one] at h1 h2
  have := lowSpanLe_mul h1 h2
  have heq : (fun z : ℂ ↦ (z.re : ℂ) ^ p * (z.im : ℂ) ^ q) =
      (fun z : ℂ ↦ (z.re : ℂ)) ^ p * (fun z : ℂ ↦ (z.im : ℂ)) ^ q := by
    funext z
    rfl
  rw [heq]
  exact this

/-- Rescaling `z ↦ √t z` preserves the degree filtration. -/
theorem lowSpanLe_comp_smul {d : ℕ} {f : ℂ → ℂ} (hf : f ∈ lowSpanLe d) (s : ℝ) :
    (fun z ↦ f ((s : ℂ) * z)) ∈ lowSpanLe d := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, hpq, rfl⟩ := hx
    have : (fun z ↦ cmon p q ((s : ℂ) * z)) = ((s : ℂ) ^ p * conj (s : ℂ) ^ q) • cmon p q := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [cmon_mul_left]
    rw [this]
    exact Submodule.smul_mem _ _ (cmon_mem_lowSpanLe hpq)
  | zero =>
    have : (fun z ↦ (0 : ℂ → ℂ) ((s : ℂ) * z)) = 0 := by
      funext z
      rfl
    rw [this]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun z ↦ (x + y) ((s : ℂ) * z)) =
        (fun z ↦ x ((s : ℂ) * z)) + fun z ↦ y ((s : ℂ) * z) := by
      funext z
      simp
    rw [this]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (fun z ↦ (a • x) ((s : ℂ) * z)) = a • fun z ↦ x ((s : ℂ) * z) := by
      funext z
      simp
    rw [this]
    exact Submodule.smul_mem _ _ hx

/-! ### Integrability and the extension to polynomials -/

theorem continuous_cycLoss (N : ℕ) (ε θ : ℝ) : Continuous (cycLoss N ε θ) := by
  unfold cycLoss
  fun_prop

theorem continuous_cmon (p q : ℕ) : Continuous (cmon p q) := by
  unfold cmon
  fun_prop

theorem continuous_of_mem_lowSpanLe {d : ℕ} {f : ℂ → ℂ} (hf : f ∈ lowSpanLe d) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, _, rfl⟩ := hx
    exact continuous_cmon p q
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

/-- A radial cutoff with compactly supported profile has compact support on `ℂ`. -/
theorem hasCompactSupport_radial {χ : ℝ → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport fun z : ℂ ↦ χ ‖z‖ := by
  obtain ⟨R, hR⟩ := hχ.isCompact.isBounded.subset_closedBall 0
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) R) (isClosed_tsupport _) ?_
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro z hz
  rw [Function.mem_support] at hz
  have hmem : ‖z‖ ∈ tsupport χ := by
    by_contra hcon
    exact hz (image_eq_zero_of_notMem_tsupport hcon)
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at this ⊢
  rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] at this

theorem continuous_cycWeight (N : ℕ) (ε : ℝ) {χ : ℝ → ℝ} (hχ : Continuous χ) (t θ : ℝ) :
    Continuous (cycWeight N ε χ t θ) := by
  unfold cycWeight
  exact Complex.continuous_ofReal.comp ((hχ.comp continuous_norm).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_cycLoss N ε θ)).neg))

theorem hasCompactSupport_cycWeight (N : ℕ) (ε : ℝ) {χ : ℝ → ℝ} (hχ : HasCompactSupport χ)
    (t θ : ℝ) : HasCompactSupport (cycWeight N ε χ t θ) := by
  unfold cycWeight
  have h := (hasCompactSupport_radial hχ).mul_right
    (f' := fun z : ℂ ↦ Real.exp (-(t * cycLoss N ε θ z)))
  exact h.comp_left Complex.ofReal_zero

theorem integrable_mul_cycWeight (N : ℕ) (ε : ℝ) {χ : ℝ → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (t θ : ℝ) {f : ℂ → ℂ} (hf : Continuous f) :
    Integrable fun z ↦ f z * cycWeight N ε χ t θ z :=
  (hf.mul (continuous_cycWeight N ε hχc t θ)).integrable_of_hasCompactSupport
    (hasCompactSupport_cycWeight N ε hχs t θ).mul_left

/-- **Every polynomial of degree `< N` has a `θ`-independent expectation**, exactly in `t`. -/
theorem cexp_eq_of_mem_lowSpanLe (N : ℕ) (hN : N ≠ 0) (ε : ℝ) {χ : ℝ → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (t θ : ℝ) {d : ℕ} (hd : d < N) {f : ℂ → ℂ}
    (hf : f ∈ lowSpanLe d) : cycExp N ε χ t θ f = cycExp N ε χ t 0 f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, hpq, rfl⟩ := hx
    exact cexp_cmon_eq N hN ε χ t θ (by omega)
  | zero => simp [cycExp]
  | add x y hx' hy' hx hy =>
    unfold cycExp at hx hy ⊢
    simp only [Pi.add_apply, add_mul]
    rw [integral_add (integrable_mul_cycWeight N ε hχc hχs t θ (continuous_of_mem_lowSpanLe hx'))
      (integrable_mul_cycWeight N ε hχc hχs t θ (continuous_of_mem_lowSpanLe hy')),
      integral_add (integrable_mul_cycWeight N ε hχc hχs t 0 (continuous_of_mem_lowSpanLe hx'))
      (integrable_mul_cycWeight N ε hχc hχs t 0 (continuous_of_mem_lowSpanLe hy')), hx, hy]
  | smul a x _ hx =>
    unfold cycExp at hx ⊢
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, integral_const_mul, hx]

/-- **Normalised rescaled expectations are `θ`-independent**: for every polynomial `P` of degree
`< N`, `E_θ[P(√t ·)] / E_θ[1] = E_0[P(√t ·)] / E_0[1]` for all `t`. -/
theorem normalized_rescaled_eq (N : ℕ) (hN : N ≠ 0) (ε : ℝ) {χ : ℝ → ℝ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (t θ : ℝ) {d : ℕ} (hd : d < N) {P : ℂ → ℂ}
    (hP : P ∈ lowSpanLe d) :
    cycExp N ε χ t θ (fun z ↦ P ((Real.sqrt t : ℂ) * z)) / cycExp N ε χ t θ (fun _ ↦ 1) =
      cycExp N ε χ t 0 (fun z ↦ P ((Real.sqrt t : ℂ) * z)) / cycExp N ε χ t 0 (fun _ ↦ 1) := by
  have h1 : (fun _ : ℂ ↦ (1 : ℂ)) ∈ lowSpanLe d := by
    have : (fun _ : ℂ ↦ (1 : ℂ)) = cmon 0 0 := by
      funext z
      simp [cmon]
    rw [this]
    exact cmon_mem_lowSpanLe (Nat.zero_le _)
  rw [cexp_eq_of_mem_lowSpanLe N hN ε hχc hχs t θ hd (lowSpanLe_comp_smul hP _),
    cexp_eq_of_mem_lowSpanLe N hN ε hχc hχs t θ hd h1]

/-! ### Headline -/

/-- **No finite family of polynomial rescaled tests identifies analytic germs in `d = 2`.** For
every degree bound `m` there is `N > m` such that the family `L_θ = ½|z|² + ε Re(e^{-iNθ}z^N) +
ε²|z|^{2N-2}` (any `ε ≠ 0`) consists of losses with a unique, nondegenerate zero at `0`
(`L_θ ≥ ¼|z|²`), a common quadratic part, pairwise distinct germs for `e^{-iNθ} ≠ e^{-iNθ'}`, and
yet identical
normalised expectations of `P(√t ·)` for every polynomial `P` of degree `≤ m`, every radial
compactly supported cutoff and every temperature. -/
theorem finite_polynomial_tests_blind (m : ℕ) :
    ∃ N : ℕ, m < N ∧ 3 ≤ N ∧ ∀ ε : ℝ, ε ≠ 0 →
      (∀ θ z, ‖z‖ ^ 2 / 4 ≤ cycLoss N ε θ z) ∧
      (∀ θ z, |cycLoss N ε θ z - ‖z‖ ^ 2 / 2| ≤ (|ε| + ε ^ 2 * ‖z‖ ^ (N - 2)) * ‖z‖ ^ N) ∧
      (∀ θ θ', Complex.exp (-((N : ℝ) * θ : ℝ) * I) ≠ Complex.exp (-((N : ℝ) * θ' : ℝ) * I) →
        ∀ δ > 0, ∃ z : ℂ, ‖z‖ < δ ∧ cycLoss N ε θ z ≠ cycLoss N ε θ' z) ∧
      (∀ (χ : ℝ → ℝ), Continuous χ → HasCompactSupport χ → ∀ (t θ : ℝ) (P : ℂ → ℂ),
        P ∈ lowSpanLe m →
        cycExp N ε χ t θ (fun z ↦ P ((Real.sqrt t : ℂ) * z)) / cycExp N ε χ t θ (fun _ ↦ 1) =
          cycExp N ε χ t 0 (fun z ↦ P ((Real.sqrt t : ℂ) * z)) / cycExp N ε χ t 0 (fun _ ↦ 1)) := by
  refine ⟨max (m + 1) 3, by omega, by omega, fun ε hε ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · intro θ z
    exact cycLoss_lower _ (by omega) ε θ z
  · intro θ z
    exact cycLoss_sub_quadratic_le _ (by omega) ε θ z
  · intro θ θ' h
    exact cycLoss_germs_differ _ (by omega) hε h
  · intro χ hχc hχs t θ P hP
    exact normalized_rescaled_eq _ (by omega) ε hχc hχs t θ (by omega) hP

end Laplace.Multi.Cyclic
