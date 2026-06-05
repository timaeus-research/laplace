import Laplace.TwoD.QuarticSexticMoments
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Rescaled asymptotic for the mixed even-power 2D moment

For the 2D separable potential $L(x, y) = x^4/24 + y^6/720$, T1's
`gibbsExpectation_quarticSextic_pow_pow_eq` gives an *exact* closed
form for $\langle x^{2j} y^{2k}\rangle_{2D, t}$ valid for all $t > 0$.
Pulling out the $t$-dependence, the moment is exactly
$C(j, k) \cdot t^{-(j/2 + k/3)}$ where
$C(j, k) = 24^{j/2} \cdot 720^{k/3} \cdot \Gamma((2j+1)/4)/\Gamma(1/4)
  \cdot \Gamma((2k+1)/6)/\Gamma(1/6)$.

This file packages that exact reformulation for downstream
asymptotic-chain consumption: a `Tendsto` form (rescaled by
$t^{j/2 + k/3}$) and an `Asymptotics.IsEquivalent` form.

## Headline

* `gibbsExpectation_quarticSextic_pow_pow_eq_const_mul_rpow` — the
  exact reformulation: moment = constant × $t^{-(j/2+k/3)}$.
* `gibbsExpectation_quarticSextic_pow_pow_rescaled_tendsto` — the
  rescaled moment tends to the constant.
* `gibbsExpectation_quarticSextic_pow_pow_isEquivalent_rpow` — the
  moment is asymptotically equivalent (at $\mathrm{atTop}$) to the
  power-law form.

## Strategy

T1 supplies the exact identity; the asymptotic packagings reduce to
"a function eventually equal to a constant tends to that constant"
(`tendsto_congr'` + `tendsto_const_nhds`) and the corresponding
asymptotic-equivalence lift via `IsEquivalent.congr_left`. No new
analysis is required; the work is pure `Real.rpow` algebraic
rearrangement.
-/

open Filter Asymptotics
open scoped Topology

namespace Laplace.TwoD

/-- The $t$-independent constant prefactor for the 2D quartic-sextic
mixed even moment:
$$
  C(j, k) := 24^{j/2} \cdot 720^{k/3}
    \cdot \frac{\Gamma((2j+1)/4)}{\Gamma(1/4)}
    \cdot \frac{\Gamma((2k+1)/6)}{\Gamma(1/6)}.
$$ -/
noncomputable def quarticSexticMomentConst (j k : ℕ) : ℝ :=
  24 ^ ((j : ℝ) / 2) * 720 ^ ((k : ℝ) / 3) *
    (Real.Gamma ((2 * j + 1 : ℝ) / 4) / Real.Gamma ((1 : ℝ) / 4)) *
    (Real.Gamma ((2 * k + 1 : ℝ) / 6) / Real.Gamma ((1 : ℝ) / 6))

/-- **Exact reformulation of T1's closed form (moment = const × `t^(-…)`).**

For the 2D potential $L(x, y) = x^4/24 + y^6/720$ at temperature
$t > 0$,
$$
  \langle x^{2j} y^{2k}\rangle_{2D, t}
  = C(j, k) \cdot t^{-(j/2 + k/3)}
$$
where $C(j, k)$ is the $t$-independent gamma-prefactor
`quarticSexticMomentConst j k`. This is an exact identity valid for
all $t > 0$, not an asymptotic; the proof is algebraic rearrangement
of T1's RHS. -/
theorem gibbsExpectation_quarticSextic_pow_pow_eq_const_mul_rpow
    (j k : ℕ) {t : ℝ} (ht : 0 < t) :
    gibbsExpectation
        (addSeparable Laplace.OneD.quarticPotential
                      Laplace.OneD.sexticPotential) t
        (fun z : ℝ × ℝ => z.1 ^ (2 * j) * z.2 ^ (2 * k))
      = quarticSexticMomentConst j k *
        t ^ (-((j : ℝ) / 2 + (k : ℝ) / 3)) := by
  rw [gibbsExpectation_quarticSextic_pow_pow_eq j k ht]
  unfold quarticSexticMomentConst
  have ht_le : (0 : ℝ) ≤ t := le_of_lt ht
  -- Split (24/t)^(j/2) and (720/t)^(k/3) into base and t-pieces.
  rw [Real.div_rpow (by norm_num : (24 : ℝ) ≥ 0) ht_le,
      Real.div_rpow (by norm_num : (720 : ℝ) ≥ 0) ht_le]
  -- Now the goal has a^(j/2)/t^(j/2) and 720^(k/3)/t^(k/3).
  -- Combine 1/t^(j/2) * 1/t^(k/3) = 1/t^(j/2+k/3) = t^(-(j/2+k/3)).
  rw [show (-((j : ℝ) / 2 + (k : ℝ) / 3)) = (-((j : ℝ) / 2)) + (-((k : ℝ) / 3)) by ring,
      Real.rpow_add ht, Real.rpow_neg ht_le, Real.rpow_neg ht_le]
  ring

/-- **Rescaled `Tendsto` form of the 2D mixed even moment.**

The moment, multiplied by $t^{j/2 + k/3}$, tends to the constant
$C(j, k)$ as $t \to \infty$. Direct consequence of the exact
reformulation: the rescaled moment is *eventually equal to a
constant function*, then `tendsto_const_nhds`. -/
theorem gibbsExpectation_quarticSextic_pow_pow_rescaled_tendsto
    (j k : ℕ) :
    Tendsto (fun t : ℝ =>
        t ^ ((j : ℝ) / 2 + (k : ℝ) / 3) *
        gibbsExpectation
          (addSeparable Laplace.OneD.quarticPotential
                        Laplace.OneD.sexticPotential) t
          (fun z : ℝ × ℝ => z.1 ^ (2 * j) * z.2 ^ (2 * k)))
      atTop (𝓝 (quarticSexticMomentConst j k)) := by
  have hEq : (fun t : ℝ =>
      t ^ ((j : ℝ) / 2 + (k : ℝ) / 3) *
      gibbsExpectation
        (addSeparable Laplace.OneD.quarticPotential
                      Laplace.OneD.sexticPotential) t
        (fun z : ℝ × ℝ => z.1 ^ (2 * j) * z.2 ^ (2 * k)))
    =ᶠ[atTop] fun _ => quarticSexticMomentConst j k := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [gibbsExpectation_quarticSextic_pow_pow_eq_const_mul_rpow j k ht]
    rw [show t ^ ((j : ℝ) / 2 + (k : ℝ) / 3) * (quarticSexticMomentConst j k *
            t ^ (-((j : ℝ) / 2 + (k : ℝ) / 3))) =
            quarticSexticMomentConst j k *
            (t ^ ((j : ℝ) / 2 + (k : ℝ) / 3) *
             t ^ (-((j : ℝ) / 2 + (k : ℝ) / 3))) from by ring]
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  exact (tendsto_const_nhds.congr' hEq.symm)

/-- **Asymptotic-equivalence form.**

The moment is asymptotically equivalent at $\mathrm{atTop}$ to the
pure power-law $C(j, k) \cdot t^{-(j/2 + k/3)}$. Direct consequence
of the exact reformulation via
`Asymptotics.IsEquivalent.refl` after `tendsto_congr'`. -/
theorem gibbsExpectation_quarticSextic_pow_pow_isEquivalent_rpow
    (j k : ℕ) :
    (fun t : ℝ =>
        gibbsExpectation
          (addSeparable Laplace.OneD.quarticPotential
                        Laplace.OneD.sexticPotential) t
          (fun z : ℝ × ℝ => z.1 ^ (2 * j) * z.2 ^ (2 * k)))
      ~[atTop]
      (fun t : ℝ => quarticSexticMomentConst j k *
                    t ^ (-((j : ℝ) / 2 + (k : ℝ) / 3))) := by
  -- The two functions are eventually equal on `atTop` (for `t > 0`),
  -- hence asymptotically equivalent.
  refine (Asymptotics.IsEquivalent.refl).congr_left ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (gibbsExpectation_quarticSextic_pow_pow_eq_const_mul_rpow j k ht).symm

end Laplace.TwoD
