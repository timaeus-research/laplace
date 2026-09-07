/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonoRepPerm

/-!
# Coefficient stability for polynomial data (Stage 4b — the stability gate)

Unit 242 (Taylor-tree programme, Stage 4; Astra #28 "single riskiest step"). The spectral
coefficients `A_{μ,j}(ξ, η)` of unit 237 are **stable under appended perturbations with a fixed
constant phase** (the situation of nested box truncations; this is not a Lipschitz statement for
arbitrary pairs of polynomial presentations measured by their functional difference), with a
constant depending only on upper bounds for the coefficient masses: if `η' ~ η ++ Δη`,
`J' ~ J ++ Δ` (`J = ξ − ξ(0)`), `ξ'(0) = ξ(0) = a`, `‖η‖₁ ≤ E`, `‖J‖₁ + ‖Δ‖₁ ≤ B`, then for `μ > 0`
```
|A_{μ,j}(ξ',η') − A_{μ,j}(ξ,η)|
  ≤ K_k D_{n,k} ( E β M_{μ+1/2,n}(a+B) ‖Δ‖₁ + M_{μ,n}(a+B) ‖Δη‖₁ ),
```
where `M_{ν,n}(b) = ∫₀^∞ t^{ν-1}(1+|log t|)^n e^{-βt+βb√t}` is the log majorant of unit 234 and
`D_{n,k} = (n+1)(n+1)! Q^n 2^n` the uniform coefficient budget (`abs_spectralCoeff_sub_le`). The
proof
is the power-difference estimate of unit 241 inside the coefficient functional, summed over phase
orders with the Tonelli identity; the factor `p` from the power difference is absorbed by shifting
the phase order (`phaseLogMoment_succ`: `M_{ν,n,p+1} = M_{ν+1/2,n,p}`). With this gate, the
coefficients of coefficient-family data (unit 243 onwards) are limits of polynomial truncations.
No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology
open scoped List

namespace Laplace.Grammar

open MonoRep

/-! ### Shifting the phase order raises the exponent by `1/2` -/

theorem logMajorant_succ (β a ν : ℝ) (r p : ℕ) {t : ℝ} (ht : 0 < t) :
    logMajorant β a ν r (p + 1) t = logMajorant β a (ν + 1 / 2) r p t := by
  unfold logMajorant phaseKernel
  rw [pow_succ, Real.sqrt_eq_rpow, show ν + 1 / 2 - 1 = (ν - 1) + 1 / 2 by ring,
    Real.rpow_add ht]
  ring

theorem phaseLogMoment_succ (β a ν : ℝ) (r p : ℕ) :
    phaseLogMoment β a ν r (p + 1) = phaseLogMoment β a (ν + 1 / 2) r p := by
  unfold phaseLogMoment
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht =>
    logMajorant_succ β a ν r p (mem_Ioi.1 ht)

/-- `∑_p β^p/p! · p · B^{p-1} · M_{ν,n,p}(a) = β · M_{ν+1/2,n}(a+B)`. -/
theorem hasSum_phase_series_shift (β a B ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (hB : 0 ≤ B) (r : ℕ) :
    HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) * ((p : ℝ) * B ^ (p - 1)) *
      phaseLogMoment β a ν r p) (β * phaseLogMoment β (a + B) (ν + 1 / 2) r 0) := by
  have hs := (summable_phaseLogMoment_series β a B (ν + 1 / 2) hβ (by linarith) hB r).hasSum
  rw [tsum_phaseLogMoment_series β a B (ν + 1 / 2) hβ (by linarith) hB r] at hs
  have hs' := hs.mul_left β
  -- re-index `q ↦ p = q + 1`
  have hshift : ∀ q : ℕ, β ^ (q + 1) / ((q + 1).factorial : ℝ) *
      (((q + 1 : ℕ) : ℝ) * B ^ (q + 1 - 1)) * phaseLogMoment β a ν r (q + 1) =
      β * ((β * B) ^ q / (q.factorial : ℝ) * phaseLogMoment β a (ν + 1 / 2) r q) := by
    intro q
    rw [phaseLogMoment_succ, Nat.add_sub_cancel, Nat.factorial_succ, mul_pow, pow_succ]
    push_cast
    field_simp
  have h0 : β ^ 0 / ((0 : ℕ).factorial : ℝ) * (((0 : ℕ) : ℝ) * B ^ (0 - 1)) *
      phaseLogMoment β a ν r 0 = 0 := by simp
  have hfun : (fun q : ℕ => β ^ (q + 1) / ((q + 1).factorial : ℝ) *
      (((q + 1 : ℕ) : ℝ) * B ^ (q + 1 - 1)) * phaseLogMoment β a ν r (q + 1)) =
      fun q => β * ((β * B) ^ q / (q.factorial : ℝ) * phaseLogMoment β a (ν + 1 / 2) r q) :=
    funext hshift
  refine (hasSum_nat_add_iff' 1).1 ?_
  rw [Finset.sum_range_one, h0, sub_zero]
  show HasSum (fun q : ℕ => β ^ (q + 1) / ((q + 1).factorial : ℝ) *
      (((q + 1 : ℕ) : ℝ) * B ^ (q + 1 - 1)) * phaseLogMoment β a ν r (q + 1))
    (β * phaseLogMoment β (a + B) (ν + 1 / 2) r 0)
  rw [hfun]
  exact hs'

/-! ### Stability of one phase-order coefficient term -/

/-- `|coeffTerm ((η ++ Δη)(J ++ Δ)^p) − coeffTerm (η J^p)|` is controlled by `‖Δ‖₁`, `‖Δη‖₁`. -/
theorem abs_coeffTerm_pert_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (η Δη J Δ : MonoRep (n + 1)) {E B : ℝ}
    (hE : l1 η ≤ E) (hB : l1 J + l1 Δ ≤ B) :
    |coeffTerm n h k β a p μ j (mul (η ++ Δη) (pow (J ++ Δ) p)) -
        coeffTerm n h k β a p μ j (mul η (pow J p))| ≤
      (∏ i, 1 / (2 * (k i : ℝ))) * ((n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        2 ^ n) * phaseLogMoment β a μ n p *
        (E * ((p : ℝ) * l1 Δ * B ^ (p - 1)) + l1 Δη * B ^ p) := by
  obtain ⟨R, hR, hl⟩ := pow_append_perm J Δ p
  set K := ∏ i, 1 / (2 * (k i : ℝ)) with hK
  set D : ℝ := (n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n with hD
  set M := phaseLogMoment β a μ n p with hM
  have hK0 : 0 ≤ K := Finset.prod_nonneg fun i _ => by positivity
  have hD0 : 0 ≤ D := by positivity
  have hM0 : 0 ≤ M := phaseLogMoment_nonneg β a μ n p
  have hB0 : 0 ≤ B := le_trans (add_nonneg (l1_nonneg J) (l1_nonneg Δ)) hB
  have hE0 : 0 ≤ E := le_trans (l1_nonneg η) hE
  have hδ : 0 ≤ l1 Δ := l1_nonneg Δ
  have hperm : (mul (η ++ Δη) (pow (J ++ Δ) p)).Perm
      ((mul η (pow J p) ++ mul η R) ++ mul Δη (pow (J ++ Δ) p)) := by
    rw [mul_append_left]
    exact ((mul_perm_right η hR).trans (mul_append_right_perm η _ R)).append_right _
  rw [coeffTerm_perm n h k β a p μ j hperm, coeffTerm_append, coeffTerm_append, add_assoc,
    add_sub_cancel_left]
  have hpow : (l1 J + l1 Δ) ^ (p - 1) ≤ B ^ (p - 1) :=
    pow_le_pow_left₀ (add_nonneg (l1_nonneg J) (l1_nonneg Δ)) hB _
  have h1 : |coeffTerm n h k β a p μ j (mul η R)| ≤
      K * D * M * (E * ((p : ℝ) * l1 Δ * B ^ (p - 1))) := by
    refine (abs_coeffTerm_le n h k hk β a hβ p hμ j _).trans ?_
    rw [l1_mul]
    have : l1 η * l1 R ≤ E * ((p : ℝ) * l1 Δ * B ^ (p - 1)) := by
      refine mul_le_mul hE (hl.trans ?_) (l1_nonneg _) hE0
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    calc K * (l1 η * l1 R) * D * M ≤ K * (E * ((p : ℝ) * l1 Δ * B ^ (p - 1))) * D * M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left this hK0) hD0) hM0
      _ = _ := by ring
  have h2 : |coeffTerm n h k β a p μ j (mul Δη (pow (J ++ Δ) p))| ≤
      K * D * M * (l1 Δη * B ^ p) := by
    refine (abs_coeffTerm_le n h k hk β a hβ p hμ j _).trans ?_
    rw [l1_mul]
    have : l1 Δη * l1 (pow (J ++ Δ) p) ≤ l1 Δη * B ^ p :=
      mul_le_mul_of_nonneg_left ((l1_pow_append_le J Δ p).trans
        (pow_le_pow_left₀ (add_nonneg (l1_nonneg J) (l1_nonneg Δ)) hB p)) (l1_nonneg _)
    calc K * (l1 Δη * l1 (pow (J ++ Δ) p)) * D * M ≤ K * (l1 Δη * B ^ p) * D * M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left this hK0) hD0) hM0
      _ = _ := by ring
  calc |coeffTerm n h k β a p μ j (mul η R) + coeffTerm n h k β a p μ j (mul Δη (pow (J ++ Δ) p))|
      ≤ _ := abs_add_le _ _
    _ ≤ K * D * M * (E * ((p : ℝ) * l1 Δ * B ^ (p - 1))) + K * D * M * (l1 Δη * B ^ p) :=
        add_le_add h1 h2
    _ = _ := by ring

/-! ### The stability gate -/

/-- The `N`-free stability constant `K_k D_{n,k}`. -/
noncomputable def stabilityPrefactor (n : ℕ) (k : Fin (n + 1) → ℕ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) *
    ((n + 1 : ℝ) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n)

/-- **Coefficient stability (Stage 4 gate).** For polynomial data with the same constant phase,
`|A_{μ,j}(ξ',η') − A_{μ,j}(ξ,η)| ≤ K_k D (E β M_{μ+1/2,n}(a+B) ‖Δ‖₁ + M_{μ,n}(a+B) ‖Δη‖₁)`. -/
theorem abs_spectralCoeff_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (ξ ξ' η η' Δη Δ : MonoRep (n + 1))
    (hη : η'.Perm (η ++ Δη)) (hJ : (fluct ξ').Perm (fluct ξ ++ Δ)) (ha : eval ξ' 0 = eval ξ 0)
    {E B : ℝ} (hE : l1 η ≤ E) (hB : l1 (fluct ξ) + l1 Δ ≤ B) :
    |spectralCoeff n h k β ξ' η' μ j - spectralCoeff n h k β ξ η μ j| ≤
      stabilityPrefactor n k *
        (E * β * phaseLogMoment β (eval ξ 0 + B) (μ + 1 / 2) n 0 * l1 Δ +
          phaseLogMoment β (eval ξ 0 + B) μ n 0 * l1 Δη) := by
  set a := eval ξ 0 with ha0
  have hB0 : 0 ≤ B := le_trans (add_nonneg (l1_nonneg _) (l1_nonneg Δ)) hB
  have hs' := summable_coeffTerm_series n h k hk β hβ μ j ξ' η'
  have hs := summable_coeffTerm_series n h k hk β hβ μ j ξ η
  unfold spectralCoeff
  rw [← hs'.tsum_sub hs]
  -- termwise perturbation bound
  have hterm : ∀ p : ℕ, ‖β ^ p / (p.factorial : ℝ) *
      coeffTerm n h k β (eval ξ' 0) p μ j (mul η' (pow (fluct ξ') p)) -
      β ^ p / (p.factorial : ℝ) * coeffTerm n h k β a p μ j (mul η (pow (fluct ξ) p))‖ ≤
      stabilityPrefactor n k * (E * l1 Δ) *
          (β ^ p / (p.factorial : ℝ) * ((p : ℝ) * B ^ (p - 1)) * phaseLogMoment β a μ n p) +
        stabilityPrefactor n k * l1 Δη *
          ((β * B) ^ p / (p.factorial : ℝ) * phaseLogMoment β a μ n p) := by
    intro p
    rw [ha, ← mul_sub, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ p / _)]
    have hperm : (mul η' (pow (fluct ξ') p)).Perm (mul (η ++ Δη) (pow (fluct ξ ++ Δ) p)) :=
      (mul_perm_left hη _).trans (mul_perm_right _ (pow_perm hJ p))
    rw [coeffTerm_perm n h k β a p μ j hperm]
    refine (mul_le_mul_of_nonneg_left (abs_coeffTerm_pert_le n h k hk β a hβ p hμ j η Δη _ Δ hE hB)
      (by positivity)).trans_eq ?_
    unfold stabilityPrefactor
    rw [mul_pow]
    ring
  have hA := (hasSum_phase_series_shift β a B μ hβ hμ hB0 n).mul_left
    (stabilityPrefactor n k * (E * l1 Δ))
  have hB' := (summable_phaseLogMoment_series β a B μ hβ hμ hB0 n).hasSum.mul_left
    (stabilityPrefactor n k * l1 Δη)
  rw [tsum_phaseLogMoment_series β a B μ hβ hμ hB0 n] at hB'
  have := tsum_of_norm_bounded (hA.add hB') hterm
  rw [Real.norm_eq_abs] at this
  refine this.trans_eq ?_
  ring

end Laplace.Grammar
