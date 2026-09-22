/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Sampler.FrobeniusTarget

/-!
# E1: the step-size trade-off, direction by direction

E1 of the note finds that against `Σ_ULA` the covariance error "simply falls with step size", while
against `P⁻¹` "the two failures trade off": the discretisation bias on the stiff directions and the
zero-start undersampling of the flat ones balance. With the exact decompositions of
`FrobeniusTarget` this is a statement about the per-direction bias terms, as functions of the step
`h` on the E4 range `0 < h ≤ 1/p`:

* `zeroStartFactor_antitone`, `ula_bias_antitone`, `ula_bias_sq_sum_antitone`: the zero-start
  bias `s₂(h) a(h)` against `Σ_ULA` is antitone in `h` (termwise
  `(1 − u')^{2m}(1 − u/2) ≤ (1 − u)^{2m}(1 − u'/2)`), and so is the bias sum of
  `frobenius_ula_target_raw`;
* `balanceGap`, `posteriorBias`, `posteriorBias_eq`: the bias against `P⁻¹` is
  `f(h) = h/(2 − hp) − s₂(h) a(h) = (hp − 2a(h)) / (p(2 − hp))`;
* `balanceGap_strictMonoOn`, `posteriorBias_tradeoff`: the gap `hp − 2a(h)` is strictly
  increasing from `−2` at `h = 0` to `1` at `h = 1/p`, so `f` has a **unique** zero `h₀ ∈ (0, 1/p)`,
  is negative below it (zero-start deflation wins) and positive above it (discretisation
  inflation wins);
* `frobenius_ula_posterior_raw_of_balanced`: when every direction is balanced the mean-square
  error against `P⁻¹` is pure Monte Carlo variance; `frobenius_ula_posterior_raw_isotropic`: for
  `κ = 1` such a step exists;
* `ula_inflation_e1`, `ula_llc_isotropic`, `ula_llc_e1`: E1's numbers `2, 4, 20` and `10, 20, 100`.
-/

open Matrix Finset MeasureTheory ProbabilityTheory

namespace Laplace.Sampler

/-! ### The bias against `Σ_ULA` falls with the step -/

section Antitone

/-- One summand of the zero-start bias, `(1 − u)^{2m} / (1 − u/2)` with `u = hp`, is antitone in `u`
on `[0, 1]` for `m ≥ 1`. -/
theorem pow_div_antitone_term {u u' : ℝ} (huu' : u ≤ u') (hu' : u' ≤ 1) {m : ℕ}
    (hm : 1 ≤ m) :
    (1 - u') ^ (2 * m) / (1 - u' / 2) ≤ (1 - u) ^ (2 * m) / (1 - u / 2) := by
  have h1 : 0 < 1 - u' / 2 := by linarith
  have h2 : 0 < 1 - u / 2 := by linarith
  rw [div_le_div_iff₀ h1 h2]
  have hp : (1 - u') ^ (2 * m - 1) ≤ (1 - u) ^ (2 * m - 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hq : (1 - u') * (1 - u / 2) ≤ (1 - u) * (1 - u' / 2) := by nlinarith
  have e : ∀ x : ℝ, x ^ (2 * m) = x ^ (2 * m - 1) * x := fun x => by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * m)]
  rw [e, e]
  calc (1 - u') ^ (2 * m - 1) * (1 - u') * (1 - u / 2)
      = (1 - u') ^ (2 * m - 1) * ((1 - u') * (1 - u / 2)) := by ring
    _ ≤ (1 - u) ^ (2 * m - 1) * ((1 - u) * (1 - u' / 2)) :=
        mul_le_mul hp hq (mul_nonneg (by linarith) (by linarith)) (pow_nonneg (by linarith) _)
    _ = (1 - u) ^ (2 * m - 1) * (1 - u) * (1 - u' / 2) := by ring

/-- The zero-start factor `a(h)` is antitone in the step on `[0, 1/p]`. -/
theorem zeroStartFactor_antitone {p h h' : ℝ} (hp : 0 < p) (hhh' : h ≤ h') (hh' : h' * p ≤ 1)
    (N b : ℕ) :
    zeroStartFactor (1 - h' * p) N b ≤ zeroStartFactor (1 - h * p) N b := by
  unfold zeroStartFactor
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
  exact pow_le_pow_left₀ (by linarith) (by nlinarith) _

/-- **The zero-start bias against `Σ_ULA` falls with the step**: `s₂(h) a(h)` is antitone in `h` on
`[0, 1/p]`, with `s₂(h) = 1/(p(1 − hp/2))`. -/
theorem ula_bias_antitone {p h h' : ℝ} (hp : 0 < p) (hhh' : h ≤ h') (hh' : h' * p ≤ 1) (N b : ℕ) :
    1 / (p * (1 - h' * p / 2)) * zeroStartFactor (1 - h' * p) N b ≤
      1 / (p * (1 - h * p / 2)) * zeroStartFactor (1 - h * p) N b := by
  unfold zeroStartFactor
  have e : ∀ u : ℝ,
      1 / (p * (1 - u / 2)) * (1 / (N : ℝ) * ∑ k ∈ range N, (1 - u) ^ (2 * (b + 1 + k))) =
        1 / p * (1 / (N : ℝ)) * ∑ k ∈ range N, (1 - u) ^ (2 * (b + 1 + k)) / (1 - u / 2) := by
    intro u
    rw [← one_div_mul_one_div]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e (h' * p), e (h * p)]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
  exact pow_div_antitone_term (mul_le_mul_of_nonneg_right hhh' hp.le) hh' (by omega)

/-- The bias sum of `frobenius_ula_target_raw`, `∑ᵢ (s₂ᵢ aᵢ)²`, is antitone in the step on
`(0, 1/p_max]`. -/
theorem ula_bias_sq_sum_antitone {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i) {h h' : ℝ}
    (hh : 0 < h) (hhh' : h ≤ h') (hh' : ∀ i, h' * p i ≤ 1) (N b : ℕ) :
    ∑ i, (2 * h' / (1 - (1 - h' * p i) ^ 2) * zeroStartFactor (1 - h' * p i) N b) ^ 2 ≤
      ∑ i, (2 * h / (1 - (1 - h * p i) ^ 2) * zeroStartFactor (1 - h * p i) N b) ^ 2 := by
  refine Finset.sum_le_sum fun i _ => ?_
  have hpi := hp i
  have hev' : h' * p i < 2 := by linarith [hh' i]
  have hev : h * p i < 2 := by nlinarith [hh' i]
  rw [ula_variance_eq (hh.trans_le hhh') hpi hev', ula_variance_eq hh hpi hev]
  refine pow_le_pow_left₀ (mul_nonneg (div_nonneg zero_le_one
    (mul_nonneg hpi.le (by linarith [hh' i]))) (zeroStartFactor_nonneg (by nlinarith [hh' i]) N b))
    ?_ 2
  exact ula_bias_antitone hpi hhh' (hh' i) N b

end Antitone

/-! ### The bias against `P⁻¹` changes sign once -/

section Balance

/-- The balance gap `hp − 2a(h)`: the numerator of the per-direction bias against `1/p`. -/
noncomputable def balanceGap (p : ℝ) (N b : ℕ) (h : ℝ) : ℝ :=
  h * p - 2 * zeroStartFactor (1 - h * p) N b

/-- The per-direction bias against `1/p`: discretisation inflation `h/(2 − hp)` minus zero-start
deflation `s₂(h) a(h)`. -/
noncomputable def posteriorBias (p : ℝ) (N b : ℕ) (h : ℝ) : ℝ :=
  h / (2 - h * p) - 1 / (p * (1 - h * p / 2)) * zeroStartFactor (1 - h * p) N b

/-- `f(h) = (hp − 2a(h)) / (p(2 − hp))`. -/
theorem posteriorBias_eq {p h : ℝ} (hp : 0 < p) (hev : h * p < 2) (N b : ℕ) :
    posteriorBias p N b h = balanceGap p N b h / (p * (2 - h * p)) := by
  unfold posteriorBias balanceGap
  have h1 : 2 - h * p ≠ 0 := by linarith
  have h2 : 1 - h * p / 2 ≠ 0 := by linarith
  field_simp

/-- The bias in the form used by `frobenius_ula_posterior_raw`. -/
theorem posteriorBias_eq_ula {p h : ℝ} (hh : 0 < h) (hp : 0 < p) (hev : h * p < 2) (N b : ℕ) :
    posteriorBias p N b h = h / (2 - h * p) -
      2 * h / (1 - (1 - h * p) ^ 2) * zeroStartFactor (1 - h * p) N b := by
  rw [posteriorBias, ula_variance_eq hh hp hev]

theorem balanceGap_zero (p : ℝ) {N : ℕ} (hN : 0 < N) (b : ℕ) : balanceGap p N b 0 = -2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [balanceGap, zeroStartFactor, hN']

theorem balanceGap_inv {p : ℝ} (hp : 0 < p) (N b : ℕ) : balanceGap p N b (1 / p) = 1 := by
  simp only [balanceGap, zeroStartFactor, one_div_mul_cancel hp.ne', sub_self]
  rw [Finset.sum_eq_zero fun k _ => zero_pow (by omega)]
  simp

theorem continuous_balanceGap (p : ℝ) (N b : ℕ) : Continuous (balanceGap p N b) := by
  unfold balanceGap zeroStartFactor
  exact (continuous_mul_const p).sub (continuous_const.mul (continuous_const.mul
    (continuous_finsetSum _ fun k _ => by fun_prop)))

/-- The balance gap is strictly increasing on `[0, 1/p]`: `hp` grows and `a(h)` falls. -/
theorem balanceGap_strictMonoOn {p : ℝ} (hp : 0 < p) (N b : ℕ) :
    StrictMonoOn (balanceGap p N b) (Set.Icc 0 (1 / p)) := by
  intro h hh h' hh' hlt
  simp only [balanceGap]
  have ha := zeroStartFactor_antitone hp hlt.le ((le_div_iff₀ hp).mp hh'.2) N b
  have : h * p < h' * p := mul_lt_mul_of_pos_right hlt hp
  linarith

/-- The gap vanishes somewhere in `(0, 1/p)`. -/
theorem balanceGap_exists_zero {p : ℝ} (hp : 0 < p) {N : ℕ} (hN : 0 < N) (b : ℕ) :
    ∃ h ∈ Set.Ioo 0 (1 / p), balanceGap p N b h = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (balanceGap p N b 0) (balanceGap p N b (1 / p)) := by
    rw [balanceGap_zero p hN b, balanceGap_inv hp N b]
    exact ⟨by norm_num, by norm_num⟩
  exact intermediate_value_Ioo (by positivity) (continuous_balanceGap p N b).continuousOn h0

/-- **The step-size trade-off along one direction.** There is a unique step `h₀ ∈ (0, 1/p)` at which
the discretisation inflation `h/(2 − hp)` and the zero-start deflation `s₂(h) a(h)` cancel; below it
the bias against `1/p` is negative (undersampling wins), above it positive (discretisation wins). -/
theorem posteriorBias_tradeoff {p : ℝ} (hp : 0 < p) {N : ℕ} (hN : 0 < N) (b : ℕ) :
    ∃! h₀, h₀ ∈ Set.Ioo 0 (1 / p) ∧ posteriorBias p N b h₀ = 0 ∧
      (∀ h, 0 ≤ h → h < h₀ → posteriorBias p N b h < 0) ∧
      (∀ h, h₀ < h → h * p ≤ 1 → 0 < posteriorBias p N b h) := by
  obtain ⟨h₀, hmem, hz⟩ := balanceGap_exists_zero hp hN b
  have hmono := balanceGap_strictMonoOn hp N b
  have hh₀ : h₀ * p ≤ 1 := (le_div_iff₀ hp).mp hmem.2.le
  have hev : ∀ {h : ℝ}, h * p ≤ 1 → h * p < 2 := fun hh => by linarith
  refine ⟨h₀, ⟨hmem, ?_, fun h hh hlt => ?_, fun h hlt hh => ?_⟩, fun h ⟨hmem', hz', _, _⟩ => ?_⟩
  · rw [posteriorBias_eq hp (hev hh₀), hz, zero_div]
  · have hhp : h * p ≤ 1 := by nlinarith
    have hg : balanceGap p N b h < 0 := by
      have := hmono ⟨hh, by linarith [hmem.2]⟩ ⟨hmem.1.le, hmem.2.le⟩ hlt
      linarith
    rw [posteriorBias_eq hp (hev hhp)]
    exact div_neg_of_neg_of_pos hg (mul_pos hp (by linarith))
  · have hg : 0 < balanceGap p N b h := by
      have := hmono ⟨hmem.1.le, hmem.2.le⟩ ⟨by linarith [hmem.1], (le_div_iff₀ hp).mpr hh⟩ hlt
      linarith
    rw [posteriorBias_eq hp (hev hh)]
    exact div_pos hg (mul_pos hp (by linarith))
  · have hhp : h * p ≤ 1 := (le_div_iff₀ hp).mp hmem'.2.le
    rw [posteriorBias_eq hp (hev hhp), div_eq_zero_iff] at hz'
    have hg : balanceGap p N b h = 0 := by
      rcases hz' with hz' | hz'
      · exact hz'
      · exact absurd hz' (mul_pos hp (by linarith)).ne'
    exact hmono.injOn (Set.Ioo_subset_Icc_self hmem') (Set.Ioo_subset_Icc_self hmem)
      (hg.trans hz.symm)

end Balance

/-! ### Consequences for the E4 error against `P⁻¹` -/

section Balanced

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Balanced directions leave only Monte Carlo variance**: if the bias against `1/pᵢ` vanishes
along every direction, the mean-square error of `Σ̂_raw` against `Q⁻¹` is its centred error. -/
theorem frobenius_ula_posterior_raw_of_balanced {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) {h : ℝ}
    (hh : 0 < h) (hev : ∀ i, h * hQ.1.eigenvalues i < 2) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N)
    (b : ℕ) (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P)
    (hzero : ∀ i, posteriorBias (hQ.1.eigenvalues i) N b h = 0) :
    ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        Q⁻¹ a a') ^ 2 ∂P =
      ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω a a' -
        ∫ ω', pooledRaw (fun c k => ulaChain Q h (ξ c) k) N b ω' a a' ∂P) ^ 2 ∂P := by
  rw [frobenius_ula_posterior_raw hQ hh hev hC hN b ξ hmeas hlaw hind]
  have : ∀ i, (h / (2 - h * hQ.1.eigenvalues i) - 2 * h / (1 - (1 - h * hQ.1.eigenvalues i) ^ 2) *
      zeroStartFactor (1 - h * hQ.1.eigenvalues i) N b) ^ 2 = 0 := fun i => by
    rw [← posteriorBias_eq_ula hh (hQ.eigenvalues_pos i) (hev i), hzero i]
    ring
  simp only [this, Finset.sum_const_zero, add_zero]

/-- **E1 at `κ = 1`**: when all eigenvalues equal `p` there is a step `h₀ ∈ (0, 1/p)` at which
the error of `Σ̂_raw` against `Q⁻¹` is pure Monte Carlo variance. -/
theorem frobenius_ula_posterior_raw_isotropic [Nonempty ι] {Q : Matrix ι ι ℝ} (hQ : Q.PosDef)
    {p : ℝ} (hiso : ∀ i, hQ.1.eigenvalues i = p) {C : ℕ} (hC : 0 < C) {N : ℕ} (hN : 0 < N) (b : ℕ)
    (ξ : Fin C → ℕ → Ω → EuclideanSpace ℝ ι) (hmeas : ∀ c k, Measurable (ξ c k))
    (hlaw : ∀ c k, P.map (ξ c k) = stdGaussian (EuclideanSpace ℝ ι))
    (hind : iIndepFun (fun a : Fin C × ℕ => ξ a.1 a.2) P) :
    ∃ h₀ ∈ Set.Ioo 0 (1 / p),
      ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h₀ (ξ c) k) N b ω a a' -
          Q⁻¹ a a') ^ 2 ∂P =
        ∫ ω, ∑ a, ∑ a', (pooledRaw (fun c k => ulaChain Q h₀ (ξ c) k) N b ω a a' -
          ∫ ω', pooledRaw (fun c k => ulaChain Q h₀ (ξ c) k) N b ω' a a' ∂P) ^ 2 ∂P := by
  have hp : 0 < p := hiso (Classical.arbitrary ι) ▸ hQ.eigenvalues_pos _
  obtain ⟨h₀, ⟨hmem, hz, -, -⟩, -⟩ := posteriorBias_tradeoff hp hN b
  have hh₀ : h₀ * p ≤ 1 := (le_div_iff₀ hp).mp hmem.2.le
  refine ⟨h₀, hmem, frobenius_ula_posterior_raw_of_balanced hQ hmem.1
    (fun i => by rw [hiso i]; linarith) hC hN b ξ hmeas hlaw hind
    (fun i => by rw [hiso i]; exact hz)⟩

end Balanced

/-! ### E1's numbers -/

section Numerics

/-- E1: "a factor 2.0 at `h p_max = 1`, 4.0 at 1.5, 20 at 1.9". -/
theorem ula_inflation_e1 :
    (1 : ℝ) / (1 - 1 / 2) = 2 ∧ (1 : ℝ) / (1 - 3 / 2 / 2) = 4 ∧
      (1 : ℝ) / (1 - 19 / 10 / 2) = 20 := by
  norm_num

/-- The ULA-corrected LLC of `ula_llc` when all eigenvalues equal `p`: `(d/2)/(1 − hp/2)`. -/
theorem ula_llc_isotropic {ι : Type*} [Fintype ι] (p h : ℝ) :
    1 / 2 * ∑ _i : ι, 1 / (1 - h * p / 2) = (Fintype.card ι / 2) / (1 - h * p / 2) := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- E1 at `κ = 1`, `d = 10`: `t⟨K⟩ = 10, 20, 100` at `h p = 1, 3/2, 19/10` against the true `5`. -/
theorem ula_llc_e1 :
    ((10 : ℝ) / 2) / (1 - 1 / 2) = 10 ∧ ((10 : ℝ) / 2) / (1 - 3 / 2 / 2) = 20 ∧
      ((10 : ℝ) / 2) / (1 - 19 / 10 / 2) = 100 := by
  norm_num

end Numerics

end Laplace.Sampler
