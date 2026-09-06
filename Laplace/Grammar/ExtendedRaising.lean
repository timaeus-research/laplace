/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Smooth

/-!
# The extended raising ladder and number operator (grammar §4 `lem:extended_ladder`)

The extension `Sneg β μ k = S_{μ - k/2}` of the fluctuation function to non-positive order
(`defn:S_negative`) satisfies the **lowering** relation definitionally (`Sneg_lowering`). Here we
prove the companion **raising** relation

  `b† S_{μ-(k+1)/2} = β^{1/2} S_{μ-k/2}`,   i.e.
  `raiseOp β (Sneg β μ (k+1)) = β^{1/2} Sneg β μ k`,

which carries the analytic content: it is proved by induction on `k` using the Weyl commutator
`[b,b†]=1` (`ladder_commutator`, applicable now that `Sneg` is `C^∞`, from `Smooth.lean`), the base
raising/lowering actions on the integral `S_μ`, and the extended lowering relation. Combining
raising after lowering yields the **number operator** on the extension,

  `b†b S_{μ-k/2} = (2(μ-k/2) - 1) S_{μ-k/2}`,

the eigenvalue relation `lem:number_operator` extended below zero. Both require the non-pole
hypothesis `μ - j/2 ≠ 0` for every positive integer `j` (`μ` not a positive half-integer). Zero
`sorry`/`axiom`; this completes the ladder structure of grammar §4.
-/

open Real

namespace Laplace.Grammar

/-- `b†(c·g) = c·(b† g)` pointwise (linearity of the raising operator in the scalar). -/
private theorem raiseOp_const_mul (β c : ℝ) (g : ℝ → ℝ) (a : ℝ) (hg : DifferentiableAt ℝ g a) :
    raiseOp β (fun a => c * g a) a = c * raiseOp β g a := by
  change β ^ (-(1 : ℝ) / 2) * deriv (fun a => c * g a) a = c * (β ^ (-(1 : ℝ) / 2) * deriv g a)
  rw [deriv_const_mul _ hg]; ring

/-- `b(c·g) = c·(b g)` pointwise (linearity of the lowering operator in the scalar). -/
private theorem lowerOp_const_mul (β c : ℝ) (g : ℝ → ℝ) (a : ℝ) (hg : DifferentiableAt ℝ g a) :
    lowerOp β (fun a => c * g a) a = c * lowerOp β g a := by
  change 2 * β ^ (-(1 : ℝ) / 2) * deriv (fun a => c * g a) a - β ^ ((1 : ℝ) / 2) * (a * (c * g a))
    = c * (2 * β ^ (-(1 : ℝ) / 2) * deriv g a - β ^ ((1 : ℝ) / 2) * (a * g a))
  rw [deriv_const_mul _ hg]; ring

/-- The Weyl commutator rearranged: `b†(b f) = b(b† f) - f` for `C²` `f`. -/
private theorem raiseOp_lowerOp (β : ℝ) (hβ : 0 < β) (f : ℝ → ℝ)
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f)) (a : ℝ) :
    raiseOp β (lowerOp β f) a = lowerOp β (raiseOp β f) a - f a := by
  have := ladder_commutator β hβ f hf1 hf2 a; linarith

/-- **Extended raising relation** (grammar §4 `lem:extended_ladder`, raising):
`b† S_{μ-(k+1)/2} = β^{1/2} S_{μ-k/2}` for the extended fluctuation function, i.e.
`raiseOp β (Sneg β μ (k+1)) = β^{1/2} Sneg β μ k`, whenever `μ` avoids the poles
`μ - j/2 = 0` (`j ≥ 1`). Proved by induction on `k`: the base uses the integral-regime actions
`b† S_μ = β^{1/2} S_{μ+1/2}` and `b S_{μ+1/2} = 2μ β^{-1/2} S_μ` together with `[b,b†]=1`; the step
replaces `b† Sneg k` by the inductive value and lowers via `Sneg_lowering`. -/
theorem raiseOp_Sneg (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ)
    (hpole : ∀ j : ℕ, 1 ≤ j → μ - (j : ℝ) / 2 ≠ 0) :
    ∀ k : ℕ, raiseOp β (fun a => Sneg β μ (k + 1) a)
      = fun a => β ^ ((1 : ℝ) / 2) * Sneg β μ k a := by
  have hββ : β ^ ((1 : ℝ) / 2) * β ^ (-(1 : ℝ) / 2) = 1 := by rw [← Real.rpow_add hβ]; norm_num
  intro k
  induction k with
  | zero =>
    funext a
    have hf1 : Differentiable ℝ (fun a => fluctuation β μ a) :=
      (contDiff_fluctuation β μ hβ hμ).differentiable (by norm_num)
    have hf2 : Differentiable ℝ (deriv (fun a => fluctuation β μ a)) :=
      ((contDiff_infty_iff_deriv.1 (contDiff_fluctuation β μ hβ hμ)).2).differentiable (by norm_num)
    have hgdiff : DifferentiableAt ℝ (lowerOp β (fun a => fluctuation β μ a)) a :=
      (contDiff_lowerOp β _ (contDiff_fluctuation β μ hβ hμ)).differentiable (by norm_num) a
    have hraise : raiseOp β (fun a => fluctuation β μ a)
        = fun a => β ^ ((1 : ℝ) / 2) * fluctuation β (μ + 1 / 2) a :=
      funext fun a => raiseOp_fluctuation β μ hβ hμ a
    have hSμp : DifferentiableAt ℝ (fun a => fluctuation β (μ + 1 / 2) a) a :=
      ((contDiff_fluctuation β (μ + 1 / 2) hβ (by linarith)).differentiable (by norm_num)) a
    set c1 : ℝ := β ^ ((1 : ℝ) / 2) / (2 * (μ - ((0 + 1 : ℕ) : ℝ) / 2)) with hc1
    have hpole1 : μ - ((0 + 1 : ℕ) : ℝ) / 2 ≠ 0 := by
      have := hpole 1 (by norm_num); simpa using this
    have hne : (2 : ℝ) * μ - 1 ≠ 0 := by
      rw [show (((0 + 1 : ℕ) : ℝ)) = 1 by norm_num] at hpole1; intro h; apply hpole1; linarith
    calc raiseOp β (fun a => Sneg β μ (0 + 1) a) a
        = c1 * raiseOp β (lowerOp β (fun a => fluctuation β μ a)) a :=
          raiseOp_const_mul β c1 (lowerOp β (fun a => fluctuation β μ a)) a hgdiff
      _ = c1 * (lowerOp β (raiseOp β (fun a => fluctuation β μ a)) a - fluctuation β μ a) := by
          rw [raiseOp_lowerOp β hβ (fun a => fluctuation β μ a) hf1 hf2 a]
      _ = c1 * (lowerOp β (fun a => β ^ ((1 : ℝ) / 2) * fluctuation β (μ + 1 / 2) a) a
              - fluctuation β μ a) := by rw [hraise]
      _ = c1 * (β ^ ((1 : ℝ) / 2) * lowerOp β (fun a => fluctuation β (μ + 1 / 2) a) a
              - fluctuation β μ a) := by
          rw [lowerOp_const_mul β (β ^ ((1 : ℝ) / 2)) (fun a => fluctuation β (μ + 1 / 2) a) a hSμp]
      _ = c1 * (β ^ ((1 : ℝ) / 2) * ((2 * (μ + 1 / 2) - 1) * β ^ (-(1 : ℝ) / 2)
              * fluctuation β (μ + 1 / 2 - 1 / 2) a) - fluctuation β μ a) := by
          rw [lowerOp_fluctuation β (μ + 1 / 2) hβ (by linarith) a]
      _ = β ^ ((1 : ℝ) / 2) * Sneg β μ 0 a := by
          rw [show μ + 1 / 2 - 1 / 2 = μ by ring, show Sneg β μ 0 a = fluctuation β μ a from rfl]
          have hcollapse : β ^ ((1 : ℝ) / 2)
              * ((2 * (μ + 1 / 2) - 1) * β ^ (-(1 : ℝ) / 2) * fluctuation β μ a)
              = (2 * μ) * fluctuation β μ a := by
            rw [show β ^ ((1 : ℝ) / 2) * ((2 * (μ + 1 / 2) - 1) * β ^ (-(1 : ℝ) / 2)
                  * fluctuation β μ a)
                = (2 * (μ + 1 / 2) - 1) * (β ^ ((1 : ℝ) / 2) * β ^ (-(1 : ℝ) / 2))
                  * fluctuation β μ a by ring, hββ]
            ring
          rw [hcollapse]
          have hc1val : c1 * (2 * μ - 1) = β ^ ((1 : ℝ) / 2) := by
            rw [hc1, show (((0 + 1 : ℕ) : ℝ)) = 1 by norm_num,
              show (2 : ℝ) * (μ - 1 / 2) = 2 * μ - 1 by ring]
            field_simp
          linear_combination (fluctuation β μ a) * hc1val
  | succ k ih =>
    funext a
    have hf1 : Differentiable ℝ (fun a => Sneg β μ (k + 1) a) :=
      differentiable_Sneg β μ hβ hμ (k + 1)
    have hf2 : Differentiable ℝ (deriv (fun a => Sneg β μ (k + 1) a)) :=
      differentiable_deriv_Sneg β μ hβ hμ (k + 1)
    have hgdiff : DifferentiableAt ℝ (lowerOp β (fun a => Sneg β μ (k + 1) a)) a :=
      (contDiff_lowerOp β _ (contDiff_Sneg β μ hβ hμ (k + 1))).differentiable (by norm_num) a
    have hSkdiff : DifferentiableAt ℝ (fun a => Sneg β μ k a) a :=
      (differentiable_Sneg β μ hβ hμ k) a
    have hlamk : μ - ((k + 1 : ℕ) : ℝ) / 2 ≠ 0 := hpole (k + 1) (by omega)
    set c2 : ℝ := β ^ ((1 : ℝ) / 2) / (2 * (μ - ((k + 1 + 1 : ℕ) : ℝ) / 2)) with hc2
    have hpoleD : (2 : ℝ) * (μ - ((k + 1 + 1 : ℕ) : ℝ) / 2) ≠ 0 := by
      have := hpole (k + 2) (by omega)
      intro h; apply this; push_cast at h ⊢; linarith
    calc raiseOp β (fun a => Sneg β μ (k + 1 + 1) a) a
        = c2 * raiseOp β (lowerOp β (fun a => Sneg β μ (k + 1) a)) a :=
          raiseOp_const_mul β c2 (lowerOp β (fun a => Sneg β μ (k + 1) a)) a hgdiff
      _ = c2 * (lowerOp β (raiseOp β (fun a => Sneg β μ (k + 1) a)) a - Sneg β μ (k + 1) a) := by
          rw [raiseOp_lowerOp β hβ (fun a => Sneg β μ (k + 1) a) hf1 hf2 a]
      _ = c2 * (lowerOp β (fun a => β ^ ((1 : ℝ) / 2) * Sneg β μ k a) a - Sneg β μ (k + 1) a) := by
          rw [ih]
      _ = c2 * (β ^ ((1 : ℝ) / 2) * lowerOp β (fun a => Sneg β μ k a) a - Sneg β μ (k + 1) a) := by
          rw [lowerOp_const_mul β (β ^ ((1 : ℝ) / 2)) (fun a => Sneg β μ k a) a hSkdiff]
      _ = c2 * (β ^ ((1 : ℝ) / 2) * ((2 * (μ - (↑k) / 2) - 1) * β ^ (-(1 : ℝ) / 2)
              * Sneg β μ (k + 1) a) - Sneg β μ (k + 1) a) := by
          rw [Sneg_lowering β μ hβ k hlamk a]
      _ = β ^ ((1 : ℝ) / 2) * Sneg β μ (k + 1) a := by
          have hcollapse : β ^ ((1 : ℝ) / 2)
              * ((2 * (μ - (↑k) / 2) - 1) * β ^ (-(1 : ℝ) / 2) * Sneg β μ (k + 1) a)
              = (2 * (μ - (↑k) / 2) - 1) * Sneg β μ (k + 1) a := by
            rw [show β ^ ((1 : ℝ) / 2)
                  * ((2 * (μ - (↑k) / 2) - 1) * β ^ (-(1 : ℝ) / 2) * Sneg β μ (k + 1) a)
                = (2 * (μ - (↑k) / 2) - 1) * (β ^ ((1 : ℝ) / 2) * β ^ (-(1 : ℝ) / 2))
                  * Sneg β μ (k + 1) a by ring, hββ]
            ring
          rw [hcollapse]
          have hden : (2 : ℝ) * μ - ((k + 1 + 1 : ℕ) : ℝ) ≠ 0 := by
            intro h; apply hpoleD
            rw [show (2 : ℝ) * (μ - ((k + 1 + 1 : ℕ) : ℝ) / 2) = 2 * μ - ((k + 1 + 1 : ℕ) : ℝ) by
              ring]
            exact h
          have hc2val : c2 * (2 * (μ - (↑k) / 2) - 2) = β ^ ((1 : ℝ) / 2) := by
            rw [hc2, show (2 : ℝ) * (μ - (↑k) / 2) - 2 = 2 * (μ - ((k + 1 + 1 : ℕ) : ℝ) / 2) by
              push_cast; ring]
            field_simp
          linear_combination (Sneg β μ (k + 1) a) * hc2val

/-- **Number operator on the extension** (grammar §4 `lem:number_operator`, extended below zero):
`b†b S_{μ-k/2} = (2(μ-k/2) - 1) S_{μ-k/2}`, i.e. `Sneg β μ k` is an eigenvector of `b†b` with
eigenvalue `2(μ-k/2) - 1`. This is raising-after-lowering: `b S_{μ-k/2} = (2(μ-k/2)-1)β^{-1/2}
S_{μ-(k+1)/2}` (`Sneg_lowering`) then `b† S_{μ-(k+1)/2} = β^{1/2} S_{μ-k/2}` (`raiseOp_Sneg`),
the `β^{±1/2}` cancelling. (With `μ - k/2 = λ + Q/2` and `N_λ = b†b - (2λ-1)`, the eigenvalue is the
number `Q`.) -/
theorem number_operator_Sneg (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ)
    (hpole : ∀ j : ℕ, 1 ≤ j → μ - (j : ℝ) / 2 ≠ 0) (k : ℕ) :
    raiseOp β (lowerOp β (fun a => Sneg β μ k a))
      = fun a => (2 * (μ - (↑k) / 2) - 1) * Sneg β μ k a := by
  have hββ : β ^ ((1 : ℝ) / 2) * β ^ (-(1 : ℝ) / 2) = 1 := by rw [← Real.rpow_add hβ]; norm_num
  have hlamk : μ - ((k + 1 : ℕ) : ℝ) / 2 ≠ 0 := hpole (k + 1) (by omega)
  have hlow : lowerOp β (fun a => Sneg β μ k a)
      = fun a => (2 * (μ - (↑k) / 2) - 1) * β ^ (-(1 : ℝ) / 2) * Sneg β μ (k + 1) a :=
    funext fun a => Sneg_lowering β μ hβ k hlamk a
  have hSk1diff : Differentiable ℝ (fun a => Sneg β μ (k + 1) a) :=
    differentiable_Sneg β μ hβ hμ (k + 1)
  funext a
  rw [hlow]
  rw [show (fun a => (2 * (μ - (↑k) / 2) - 1) * β ^ (-(1 : ℝ) / 2) * Sneg β μ (k + 1) a)
      = fun a => ((2 * (μ - (↑k) / 2) - 1) * β ^ (-(1 : ℝ) / 2)) * Sneg β μ (k + 1) a from by
        funext a; ring,
    raiseOp_const_mul β ((2 * (μ - (↑k) / 2) - 1) * β ^ (-(1 : ℝ) / 2))
      (fun a => Sneg β μ (k + 1) a) a (hSk1diff a),
    show raiseOp β (fun a => Sneg β μ (k + 1) a) a = β ^ ((1 : ℝ) / 2) * Sneg β μ k a from
      congrFun (raiseOp_Sneg β μ hβ hμ hpole k) a]
  rw [show (2 * (μ - (↑k) / 2) - 1) * β ^ (-(1 : ℝ) / 2) * (β ^ ((1 : ℝ) / 2) * Sneg β μ k a)
      = (2 * (μ - (↑k) / 2) - 1) * (β ^ ((1 : ℝ) / 2) * β ^ (-(1 : ℝ) / 2)) * Sneg β μ k a by ring,
    hββ]
  ring

end Laplace.Grammar
