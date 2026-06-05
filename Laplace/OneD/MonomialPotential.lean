import Laplace.Gibbs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Pure even-monomial 1D Gibbs moments (generic $k$)

For the centred even-monomial potential $L_k(x) = x^{2k}/(2k)!$ with
$k \ge 1$, this file establishes exact closed forms for the moments
and the partition function of the 1D Gibbs measure
$\exp(-t \cdot L_k(x))\,dx$. The quartic case ($k = 2$) and sextic
case ($k = 3$) become specialisations of the generic statement; the
1D ingredients used by today's V2/Z1/Z2 trio (on the 2D quartic-sextic
potential) lift to arbitrary $k$ via this file.

## Headline results

* `kth_moment_even` :
  $\int x^{2j} \cdot \exp(-t \cdot x^{2k}/(2k)!) \,dx
   = (1/k) \cdot ((2k)!/t)^{(2j+1)/(2k)} \cdot \Gamma((2j+1)/(2k))$.
* `kth_moment_odd` :
  $\int x^{2j+1} \cdot \exp(-t \cdot x^{2k}/(2k)!) \,dx = 0$.
* `partitionFunction_kthPotential` :
  $Z_{L_k}(t) = (1/k) \cdot ((2k)!/t)^{1/(2k)} \cdot \Gamma(1/(2k))$.
* `gibbsExpectation_kthPotential_even` :
  $\langle x^{2j}\rangle_{L_k, t}
   = ((2k)!/t)^{j/k} \cdot \Gamma((2j+1)/(2k)) / \Gamma(1/(2k))$.
* `gibbsExpectation_kthPotential_odd` : zero.

## Strategy

Apply Mathlib's `integral_rpow_mul_exp_neg_mul_rpow` with $p = 2k$,
$q = 2j$, $b = t/(2k)!$ to get the half-line closed form; double via
`integral_comp_abs` for the full real line. Odd moments vanish by
odd reflection symmetry. The partition is the specialisation
$j = 0$. The expected values are numerator over partition.

## Integrability

The integrability witnesses (`kth_integrable_pow` /
`kth_integrable_pow_pot`) are proved below, *uniformly for all* $k \ge 1$:
the Gaussian-domination argument goes through the bound
$x^2 \le 1 + x^{2k}$ (`sq_le_one_add_pow_two_mul`), which holds for every
$k \ge 1$ without a $k = 1$ vs $k \ge 2$ case split. Downstream consumers
can use these generic lemmas directly, or the fixed-$k$
`quartic_integrable_pow*` / `sextic_integrable_pow*` specialisations.
-/

open Real MeasureTheory Set

namespace Laplace.OneD

/-- The 1D pure even-monomial potential $L_k(x) = x^{2k}/(2k)!$. -/
noncomputable def kthPotential (k : ℕ) : ℝ → ℝ :=
  fun x => x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)

@[simp] lemma kthPotential_apply (k : ℕ) (x : ℝ) :
    kthPotential k x = x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) := rfl

/-! ## Integrability -/

/-- Key bound for the generic-$k$ Gaussian-domination argument:
$x^2 \le 1 + x^{2k}$ for any $k \ge 1$. -/
private lemma sq_le_one_add_pow_two_mul (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    x ^ 2 ≤ 1 + x ^ (2 * k) := by
  rcases le_total (x ^ 2) 1 with hx | hx
  · -- $|x| \le 1$: $x^2 \le 1 \le 1 + x^{2k}$ since $x^{2k} \ge 0$.
    have h : (0 : ℝ) ≤ x ^ (2 * k) := by
      rw [pow_mul]; exact pow_nonneg (sq_nonneg x) k
    linarith
  · -- $|x| \ge 1$: $x^{2k} = (x^2)^k \ge x^2$ since $1 \le x^2$ and $1 \le k$.
    have hpow : x ^ (2 * k) = (x ^ 2) ^ k := by rw [pow_mul]
    have hge : x ^ 2 ≤ (x ^ 2) ^ k :=
      le_self_pow₀ hx (Nat.one_le_iff_ne_zero.mp hk)
    rw [hpow]; linarith

/-- Polynomial-times-monomial-Gibbs integrability. For $k \ge 1$,
$n : \mathbb N$, and $t > 0$, $x^n \cdot \exp(-t \cdot x^{2k}/(2k)!)$ is
Lebesgue integrable on $\mathbb R$.

Proof: Gaussian comparison via $x^2 \le 1 + x^{2k}$, which gives
$t \cdot x^{2k}/(2k)! \ge (t/(2k)!) \cdot x^2 - t/(2k)!$, hence
$\exp(-t x^{2k}/(2k)!) \le \exp(t/(2k)!) \cdot \exp(-(t/(2k)!) x^2)$.
The dominator is integrable by Mathlib's
`integrable_rpow_mul_exp_neg_mul_sq` with $b = t/(2k)!$. -/
theorem kth_integrable_pow
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ =>
      x ^ n * Real.exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) := by
  set fac : ℝ := (Nat.factorial (2 * k) : ℝ) with hfac_def
  have hfac_pos : (0 : ℝ) < fac := by
    change (0 : ℝ) < (Nat.factorial (2 * k) : ℝ)
    exact_mod_cast Nat.factorial_pos _
  have ht_fac : (0 : ℝ) < t / fac := div_pos ht hfac_pos
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => x ^ n * Real.exp (-(t * x ^ (2 * k) / fac))) volume :=
    (by fun_prop : Continuous _).aestronglyMeasurable
  have hns : (-1 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hdom_raw : Integrable
      (fun x : ℝ => x ^ ((n : ℕ) : ℝ) * Real.exp (-(t / fac) * x ^ 2)) volume :=
    integrable_rpow_mul_exp_neg_mul_sq ht_fac hns
  have hdom : Integrable
      (fun x : ℝ => x ^ n * Real.exp (-((t / fac) * x ^ 2))) volume := by
    have heq : (fun x : ℝ => x ^ ((n : ℕ) : ℝ) * Real.exp (-(t / fac) * x ^ 2)) =
               (fun x : ℝ => x ^ n * Real.exp (-((t / fac) * x ^ 2))) := by
      ext x
      rw [Real.rpow_natCast]
      congr 2
      ring
    rwa [heq] at hdom_raw
  have hbound : ∀ x : ℝ,
      Real.exp (-(t * x ^ (2 * k) / fac)) ≤
        Real.exp (t / fac) * Real.exp (-((t / fac) * x ^ 2)) := by
    intro x
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hkey : x ^ 2 ≤ 1 + x ^ (2 * k) := sq_le_one_add_pow_two_mul k hk x
    have hfac_ne : fac ≠ 0 := ne_of_gt hfac_pos
    have hrewrite : t * x ^ (2 * k) / fac = (t / fac) * x ^ (2 * k) := by
      field_simp
    rw [hrewrite]
    have hprod : (0 : ℝ) ≤ (t / fac) * (1 + x ^ (2 * k) - x ^ 2) :=
      mul_nonneg ht_fac.le (by linarith)
    nlinarith
  have habs : ∀ x : ℝ,
      ‖x ^ n * Real.exp (-(t * x ^ (2 * k) / fac))‖ ≤
        ‖Real.exp (t / fac) * (x ^ n * Real.exp (-((t / fac) * x ^ 2)))‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _), abs_pow]
    have hxn : (0 : ℝ) ≤ |x| ^ n := pow_nonneg (abs_nonneg _) n
    nlinarith [hbound x, Real.exp_pos (-((t / fac) * x ^ 2))]
  exact (hdom.const_mul (Real.exp (t / fac))).mono hmeas
    (Filter.Eventually.of_forall habs)

/-- Polynomial-times-monomial-Gibbs integrability, in `kthPotential` form. -/
theorem kth_integrable_pow_pot
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-(t * kthPotential k x))) := by
  have h := kth_integrable_pow hk n ht
  have heq : (fun x : ℝ =>
      x ^ n * Real.exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) =
             (fun x : ℝ => x ^ n * Real.exp (-(t * kthPotential k x))) := by
    ext x
    rw [kthPotential_apply]
    congr 2
    ring
  rwa [heq] at h

/-! ## Half-line moment integral -/

/-- Half-line moment integral against the pure even-monomial Gibbs
weight. For $k \ge 1$, $j : \mathbb N$, and $t > 0$,
$$
  \int_0^\infty x^{2j} \cdot \exp\!\left(-t\cdot \tfrac{x^{2k}}{(2k)!}\right) dx
    = \tfrac{1}{2k}\,\left(\tfrac{(2k)!}{t}\right)^{(2j+1)/(2k)}\,
      \Gamma\!\left(\tfrac{2j+1}{2k}\right).
$$
Direct application of `integral_rpow_mul_exp_neg_mul_rpow` with
$p = 2k$, $q = 2j$, $b = t/(2k)!$. -/
theorem integral_pow_mul_exp_neg_kth_Ioi
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * j) *
        exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) =
      (1 / ((2 * k : ℕ) : ℝ)) *
        ((Nat.factorial (2 * k) : ℝ) / t) ^
          ((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) *
        Real.Gamma ((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
  set p : ℕ := 2 * k with hp_def
  have hp_pos : 0 < p := by change 0 < 2 * k; omega
  set pR : ℝ := (p : ℝ) with hpR_def
  have hpR_pos : (0 : ℝ) < pR := by
    change (0 : ℝ) < (p : ℝ); exact_mod_cast hp_pos
  set fac : ℝ := (Nat.factorial p : ℝ) with hfac_def
  have hfac_pos : (0 : ℝ) < fac := by
    change (0 : ℝ) < (Nat.factorial p : ℝ)
    exact_mod_cast Nat.factorial_pos _
  have ht_fac : (0 : ℝ) < t / fac := div_pos ht hfac_pos
  have hq : (-1 : ℝ) < 2 * (j : ℝ) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  -- Master lemma at p = pR, q = 2j, b = t/fac.
  have key := integral_rpow_mul_exp_neg_mul_rpow
    (p := pR) (q := 2 * (j : ℝ)) (b := t / fac)
    hpR_pos hq ht_fac
  -- Massage our npow / Nat-cast integrand to the rpow form Mathlib uses.
  have hLHS : (∫ x in Ioi (0 : ℝ), x ^ (2 * j) *
                  exp (-(t * x ^ p / fac))) =
      ∫ x in Ioi (0 : ℝ), x ^ (2 * (j : ℝ)) *
        exp (-(t / fac) * x ^ pR) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [mem_Ioi] at hx
    have hxnn : (0 : ℝ) ≤ x := le_of_lt hx
    have h2j : x ^ (2 * (j : ℝ)) = x ^ (2 * j) := by
      rw [show (2 * (j : ℝ) : ℝ) = ((2 * j : ℕ) : ℝ) by push_cast; ring,
          rpow_natCast]
    have hpRpow : x ^ pR = x ^ p := by rw [hpR_def, Real.rpow_natCast]
    rw [h2j, hpRpow]
    congr 2
    field_simp
  rw [hLHS, key]
  -- Reduce the rpow exponent (2j+1)/pR to canonical form (and handle the negation).
  have hg : (2 * (j : ℝ) + 1) / pR = (2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ) := by
    rw [hpR_def, hp_def]
  have hgneg : -(2 * (j : ℝ) + 1) / pR =
      -((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
    rw [hpR_def, hp_def]; ring
  rw [hg, hgneg]
  -- Convert (t/fac)^(-(2j+1)/(2k)) to (fac/t)^((2j+1)/(2k)).
  have hinv : (t / fac : ℝ) ^ (-((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ))) =
      (fac / t : ℝ) ^ ((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
    rw [show (fac / t : ℝ) = (t / fac)⁻¹ by field_simp]
    rw [inv_rpow ht_fac.le, ← Real.rpow_neg ht_fac.le]
  rw [hinv]
  -- Final goal: (fac/t)^... * (1/pR) * Γ(...) = (1/(2k:ℕ:ℝ)) * (fac/t)^... * Γ(...)
  -- The factor (1/pR) = (1/(2k:ℕ:ℝ)) because pR = ((2k:ℕ):ℝ).
  rw [hpR_def, hp_def]
  ring

/-! ## Full-line moment integrals -/

/-- Full-line even moment of the pure even-monomial Gibbs weight.
For $k \ge 1$, $j : \mathbb N$, and $t > 0$,
$$
  \int_{\mathbb R} x^{2j}\cdot \exp\!\left(-t\cdot\tfrac{x^{2k}}{(2k)!}\right) dx
    = \tfrac{1}{k}\,\left(\tfrac{(2k)!}{t}\right)^{(2j+1)/(2k)}\,
      \Gamma\!\left(\tfrac{2j+1}{2k}\right).
$$ -/
theorem kth_moment_even
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, x ^ (2 * j) *
        exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) =
      (1 / (k : ℝ)) *
        ((Nat.factorial (2 * k) : ℝ) / t) ^
          ((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) *
        Real.Gamma ((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
  -- Step 1: rewrite the integrand in |x|-form (integrand is even in x).
  have heven : (∫ x : ℝ, x ^ (2 * j) *
                  exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) =
      ∫ x : ℝ, |x| ^ (2 * j) *
        exp (-(t * |x| ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) := by
    congr 1
    ext x
    rw [show x ^ (2 * j) = |x| ^ (2 * j) from by
          rw [pow_mul x 2 j, ← sq_abs x, ← pow_mul],
        show x ^ (2 * k) = |x| ^ (2 * k) from by
          rw [pow_mul x 2 k, ← sq_abs x, ← pow_mul]]
  rw [heven]
  -- Step 2: integral_comp_abs gives 2 × half-line integral.
  rw [integral_comp_abs (f := fun y => y ^ (2 * j) *
        exp (-(t * y ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))))]
  -- Step 3: substitute the half-line value.
  rw [integral_pow_mul_exp_neg_kth_Ioi hk j ht]
  -- Step 4: combine the factor of 2 with 1/(2k) to get 1/k.
  have hk_pos : (0 : ℝ) < k := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hk)
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have h2k_eq : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
  rw [h2k_eq]
  field_simp

/-- Full-line odd moment of the pure even-monomial Gibbs weight vanishes
by symmetry. For $k, j : \mathbb N$ and any $t : \mathbb R$,
$\int x^{2j+1}\cdot \exp(-t \cdot x^{2k}/(2k)!) \,dx = 0$. -/
theorem kth_moment_odd (k j : ℕ) (t : ℝ) :
    ∫ x : ℝ, x ^ (2 * j + 1) *
        exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) = 0 := by
  set f : ℝ → ℝ := fun x => x ^ (2 * j + 1) *
      exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))) with hf
  have hodd : ∀ x : ℝ, f (-x) = -(f x) := by
    intro x
    simp only [hf]
    rw [Odd.neg_pow ⟨j, rfl⟩,
        show ((-x) : ℝ) ^ (2 * k) = x ^ (2 * k) from by
          rw [pow_mul (-x) 2 k, neg_sq, ← pow_mul]]
    ring
  have heq : (∫ x, f x) = -(∫ x, f x) := by
    conv_lhs => rw [← integral_neg_eq_self f volume]
    rw [show (fun x => f (-x)) = (fun x => -(f x)) from funext hodd]
    rw [integral_neg]
  linarith

/-! ## Partition function in `partitionFunction (kthPotential k) t` form -/

/-- The partition function for the pure even-monomial potential
$L_k(x) = x^{2k}/(2k)!$ in `partitionFunction`-form.
For $k \ge 1$ and $t > 0$,
$$
  Z_{L_k}(t) = \tfrac{1}{k}\,\left(\tfrac{(2k)!}{t}\right)^{1/(2k)}\,
    \Gamma\!\left(\tfrac{1}{2k}\right).
$$ -/
theorem partitionFunction_kthPotential
    {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    partitionFunction (kthPotential k) t =
      (1 / (k : ℝ)) *
        ((Nat.factorial (2 * k) : ℝ) / t) ^ ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) *
        Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
  unfold partitionFunction
  -- Rewrite ∫ exp(-(t · kthPotential k x)) as the j = 0 case of kth_moment_even.
  have step : (∫ x : ℝ, exp (-(t * kthPotential k x))) =
              (∫ x : ℝ, x ^ (2 * 0) *
                exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) := by
    congr 1
    ext x
    rw [Nat.mul_zero, pow_zero, one_mul, kthPotential_apply]
    congr 1; ring
  rw [step, kth_moment_even hk 0 ht]
  -- (2 * ↑0 + 1) = 1 (as ℝ); normalise the rpow exponent and Gamma argument.
  norm_num

/-- The partition function for the pure even-monomial potential is positive. -/
theorem partitionFunction_kthPotential_pos
    {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    0 < partitionFunction (kthPotential k) t := by
  rw [partitionFunction_kthPotential hk ht]
  have hk_pos : (0 : ℝ) < k := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hk)
  have h2k_pos : 0 < ((2 * k : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * k := by omega
    exact_mod_cast this
  have hα_pos : 0 < (1 : ℝ) / ((2 * k : ℕ) : ℝ) := div_pos one_pos h2k_pos
  have hfac_pos : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hfac_t_pos : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) / t := div_pos hfac_pos ht
  have h_rpow_pos : (0 : ℝ) < ((Nat.factorial (2 * k) : ℝ) / t) ^
      ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := Real.rpow_pos_of_pos hfac_t_pos _
  have hΓ_pos : 0 < Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos hα_pos
  positivity

/-! ## Expected values -/

/-- Even-power expected value against the pure even-monomial Gibbs measure.
For $k \ge 1$, $j : \mathbb N$, and $t > 0$,
$$
  \langle x^{2j}\rangle_{L_k, t}
    = \left(\tfrac{(2k)!}{t}\right)^{j/k}\,
      \tfrac{\Gamma((2j+1)/(2k))}{\Gamma(1/(2k))}.
$$ -/
theorem gibbsExpectation_kthPotential_even
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation (kthPotential k) t (fun x => x ^ (2 * j)) =
      ((Nat.factorial (2 * k) : ℝ) / t) ^ ((j : ℝ) / (k : ℝ)) *
        Real.Gamma ((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) /
        Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) := by
  unfold gibbsExpectation
  -- Numerator: kth_moment_even (after unfolding kthPotential).
  have hnum : (∫ x : ℝ, x ^ (2 * j) *
                exp (-(t * kthPotential k x))) =
              (∫ x : ℝ, x ^ (2 * j) *
                exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) := by
    congr 1; ext x
    rw [kthPotential_apply]
    congr 2; ring
  rw [hnum, kth_moment_even hk j ht, partitionFunction_kthPotential hk ht]
  -- After substitution: (1/k * (fac/t)^((2j+1)/(2k)) * Γ_num) /
  --                     (1/k * (fac/t)^(1/(2k)) * Γ_den)
  --                   = (fac/t)^((2j+1)/(2k) - 1/(2k)) * Γ_num / Γ_den
  --                   = (fac/t)^(2j/(2k)) * Γ_num / Γ_den
  --                   = (fac/t)^(j/k) * Γ_num / Γ_den
  have hk_pos : (0 : ℝ) < k := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hk)
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have h2k_pos : 0 < ((2 * k : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * k := by omega
    exact_mod_cast this
  have h2k_ne : ((2 * k : ℕ) : ℝ) ≠ 0 := ne_of_gt h2k_pos
  have hfac_pos : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hfac_t_pos : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) / t := div_pos hfac_pos ht
  -- Split the rpow: (fac/t)^((2j+1)/(2k)) = (fac/t)^(1/(2k)) * (fac/t)^(j/k).
  have hexp_split : ((2 * j + 1 : ℝ) / ((2 * k : ℕ) : ℝ)) =
                    ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) + ((j : ℝ) / (k : ℝ)) := by
    have h2k_eq : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    rw [h2k_eq]; field_simp; ring
  rw [hexp_split, Real.rpow_add hfac_t_pos]
  have hΓ_pos : 0 < Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) :=
    Real.Gamma_pos_of_pos (div_pos one_pos h2k_pos)
  have hΓ_ne : Real.Gamma ((1 : ℝ) / ((2 * k : ℕ) : ℝ)) ≠ 0 := ne_of_gt hΓ_pos
  field_simp

/-- Odd-power expected value against the pure even-monomial Gibbs measure
vanishes by symmetry. For $k, j : \mathbb N$ and any $t : \mathbb R$,
$\langle x^{2j+1}\rangle_{L_k, t} = 0$. -/
theorem gibbsExpectation_kthPotential_odd (k j : ℕ) (t : ℝ) :
    gibbsExpectation (kthPotential k) t (fun x => x ^ (2 * j + 1)) = 0 := by
  unfold gibbsExpectation
  have hnum : (∫ x : ℝ, x ^ (2 * j + 1) *
                exp (-(t * kthPotential k x))) =
              (∫ x : ℝ, x ^ (2 * j + 1) *
                exp (-(t * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)))) := by
    congr 1; ext x
    rw [kthPotential_apply]
    congr 2; ring
  rw [hnum, kth_moment_odd k j t, zero_div]

end Laplace.OneD
