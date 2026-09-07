/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.TaylorTreeAsymptotic

/-!
# Spectral support on the paper's candidate set (Stage 3j)

Unit 240 (Taylor-tree programme; review v20 should-fix 1, 2, 6; Astra #28 candidate B). The
expansions of units 237–239 are indexed by the ambient lattice `Λ_L = latticeBelow (2∏kᵢ) L`. Here
the paper's **candidate exponent set**
```
Λ(h,k) = ⋃_i ((hᵢ+1)/(2kᵢ) + (1/(2kᵢ)) ℕ)          (`candidateExp h k`)
```
is defined verbatim, and the spectral coefficients are shown to **vanish off it**
(`spectralCoeff_eq_zero_of_not_candidate`; in particular at `μ ≤ 0`): every exponent of the
state
density of `u^{h+γ}` is `(hᵢ+γᵢ+1)/(2kᵢ)`, so the aggregated coefficient `coeffAt` is zero at any
other
`μ`, for every monomial, every phase order and hence for the whole series. Consequently the spectral
sum can be restricted to `Λ(h,k) ∩ [0,L)` (`spectralSum_eq_candidate`) and Headline XXVI holds over
the paper's set (`taylorTree_isBigO_candidate`). Also exported: the explicit coefficient formula
(`spectralCoeff_eq`; the paper's `C_{μ,m}` is `A_{μ,m-1}`) and the summed exponential low-spectrum
tail bound `|tailSeries| ≤ C (1+log N)^n e^{-βN/4}` (`abs_tailSeries_le_exp`). Scope as in Stage 3:
polynomial `ξ, η`, unit box, `β > 0`, `kᵢ > 0`. No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Laplace.Grammar

open MonoRep

/-- The paper's candidate exponent set `Λ(h,k) = ⋃_i ((hᵢ+1)/(2kᵢ) + (1/(2kᵢ))ℕ)`. -/
def candidateExp {d : ℕ} (h k : Fin d → ℕ) (μ : ℝ) : Prop :=
  ∃ (i : Fin d) (r : ℕ), μ = ((h i : ℝ) + r + 1) / (2 * (k i : ℝ))

theorem candidateExp_pos {d : ℕ} {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : candidateExp h k μ) : 0 < μ := by
  obtain ⟨i, r, rfl⟩ := hμ
  have := hk i
  positivity

/-- `Λ(h,k) ⊆ Q⁻¹ℕ` with `Q = 2∏kᵢ`. -/
theorem candidateExp_mem_lattice {d : ℕ} {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : candidateExp h k μ) : ∃ m : ℕ, μ = (m : ℝ) / latticeQ k := by
  obtain ⟨i, r, rfl⟩ := hμ
  obtain ⟨m, -, hm⟩ := ratio_mem_lattice k hk i (h i + r)
  refine ⟨m, ?_⟩
  rw [← hm]
  push_cast
  ring

/-- Every exponent of the state density of `u^{h+γ}` lies in `Λ(h,k)`. -/
theorem stateDensityRep_monoWeights_candidate (n : ℕ) (h k γ : Fin (n + 1) → ℕ) :
    ∀ t ∈ stateDensityRep n (monoWeights (h + γ) k), candidateExp h k t.1 := by
  intro t ht
  obtain ⟨i, hi⟩ := stateDensityRep_exponent_mem n _ t ht
  refine ⟨i, γ i, ?_⟩
  rw [hi]
  unfold monoWeights
  rw [sub_add_cancel, Pi.add_apply]
  push_cast
  ring

theorem coeffAt_monoWeights_eq_zero (n : ℕ) (h k γ : Fin (n + 1) → ℕ) {μ : ℝ}
    (hμ : ¬ candidateExp h k μ) (q : ℕ) :
    PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q = 0 :=
  coeffAt_eq_zero_of_forall_ne _ (fun t ht heq => by
    have := stateDensityRep_monoWeights_candidate n h k γ t ht
    rw [heq] at this
    exact hμ this) q

theorem coeffTerm_eq_zero_of_not_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ)
    {μ : ℝ} (hμ : ¬ candidateExp h k μ) (j : ℕ) (P : MonoRep (n + 1)) :
    coeffTerm n h k β a p μ j P = 0 := by
  unfold coeffTerm
  rw [mul_eq_zero]
  right
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx
  rw [Finset.sum_eq_zero fun q _ => by rw [coeffAt_monoWeights_eq_zero n h k s.1 hμ q]; ring,
    mul_zero]

/-- **Spectral support**: the coefficient `A_{μ,j}` vanishes unless `μ ∈ Λ(h,k)`. -/
theorem spectralCoeff_eq_zero_of_not_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (ξ η : MonoRep (n + 1)) {μ : ℝ} (hμ : ¬ candidateExp h k μ) (j : ℕ) :
    spectralCoeff n h k β ξ η μ j = 0 := by
  unfold spectralCoeff
  simp_rw [coeffTerm_eq_zero_of_not_candidate n h k β _ _ hμ j, mul_zero, tsum_zero]

/-- In particular `A_{μ,j} = 0` for `μ ≤ 0` (the lattice point `0 ∈ Λ_L` carries nothing). -/
theorem spectralCoeff_eq_zero_of_nonpos (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (ξ η : MonoRep (n + 1)) {μ : ℝ} (hμ : μ ≤ 0) (j : ℕ) :
    spectralCoeff n h k β ξ η μ j = 0 :=
  spectralCoeff_eq_zero_of_not_candidate n h k β ξ η
    (fun hc => absurd (candidateExp_pos hk hc) (not_lt.2 hμ)) j

/-- **The explicit coefficient formula** (the paper's `C_{μ,m}` is `A_{μ,m-1}`):
`A_{μ,j} = ∑_p β^p/p! · ∏ 1/(2kᵢ) · ∑_{(γ,c) ∈ η J^p} c ∑_{q=j}^{n} coeffAt(ρ_{h+γ}, μ, q) C(q,j)
fluctMoment β ξ(0) p μ (q-j)`, with
`fluctMoment β a p μ i = ∫₀^∞ t^{μ-1}(-log t)^i (√t)^p e^{-βt+βa√t}`
(interpretation: `= (−∂_μ)^i S_{μ+p/2}(a) = β^{-p} (−∂_μ)^i ∂_a^p S_μ(a)`, not a formal theorem). -/
theorem spectralCoeff_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (ξ η : MonoRep (n + 1))
    (μ : ℝ) (j : ℕ) :
    spectralCoeff n h k β ξ η μ j = ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
      ((∏ i, 1 / (2 * (k i : ℝ))) * ((mul η (pow (fluct ξ) p)).map fun s =>
        s.2 * ∑ q ∈ Finset.Ico j (n + 1),
          PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + s.1) k)) μ q *
            (q.choose j : ℝ) * fluctMoment β (eval ξ 0) p μ (q - j)).sum) := rfl

open Classical in
/-- The spectral sum restricted to the paper's candidate set `Λ(h,k) ∩ [0,L)`. -/
theorem spectralSum_eq_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (β L : ℝ)
    (ξ η : MonoRep (n + 1)) (N : ℝ) :
    spectralSum n h k β L ξ η N =
      ∑ μ ∈ (latticeBelow (latticeQ k) L).filter (candidateExp h k), N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), spectralCoeff n h k β ξ η μ j * (Real.log N) ^ j := by
  unfold spectralSum
  symm
  refine Finset.sum_filter_of_ne fun μ _ hne => ?_
  by_contra hμ
  refine hne ?_
  rw [Finset.sum_eq_zero fun j _ => by
    rw [spectralCoeff_eq_zero_of_not_candidate n h k β ξ η hμ j, zero_mul], mul_zero]

open Classical in
/-- **Headline XXVI over the paper's candidate set**: `Z(N) − ∑_{μ ∈ Λ(h,k), μ < L} N^{-μ}
∑_{j ≤ n} A_{μ,j} (log N)^j = O(N^{-L} (1+log N)^n)`. -/
theorem taylorTree_isBigO_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) (ξ η : MonoRep (n + 1)) :
    (fun N : ℝ => polyPhaseIntegral n h k β N ξ η -
      ∑ μ ∈ (latticeBelow (latticeQ k) L).filter (candidateExp h k), N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), spectralCoeff n h k β ξ η μ j * (Real.log N) ^ j) =O[atTop]
      fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n := by
  refine (taylorTree_isBigO n h k hk β hβ hL ξ η).congr_left fun N => ?_
  rw [spectralSum_eq_candidate]

/-- **Summed exponential low-spectrum tail**: `|tailSeries| ≤ C (1+log N)^n e^{-βN/4}` (the paper's
`O(e^{-εn})` tail replacement, for every `ε < β/4`). -/
theorem abs_tailSeries_le_exp (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (ξ η : MonoRep (n + 1)) :
    |tailSeries n h k β N L ξ η| ≤
      ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) *
        (tailConst β (eval ξ 0 + l1 (fluct ξ)) 0 L n * (4 / β))) *
        ((1 + Real.log N) ^ n * Real.exp (-(β * N / 4))) := by
  have h1 := tsum_of_norm_bounded (hasSum_tailMajorant n k β hβ hL hN ξ η)
    (tailTerm_le n h k hk β hβ hL hN ξ η)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have hpre : 0 ≤ (∏ i, 1 / (2 * (k i : ℝ))) * l1 η *
      (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * (1 + Real.log N) ^ n :=
    mul_nonneg (mul_nonneg (mul_nonneg hK (l1_nonneg η)) (by positivity))
      (pow_nonneg (by linarith [Real.log_nonneg hN]) _)
  calc _ ≤ ((∏ i, 1 / (2 * (k i : ℝ))) * l1 η *
        (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * (1 + Real.log N) ^ n) *
        (tailConst β (eval ξ 0 + l1 (fluct ξ)) 0 L n * (4 / β) * Real.exp (-(β * N / 4))) :=
        mul_le_mul_of_nonneg_left (logTailMoment_le β _ L hβ n hN) hpre
    _ = _ := by ring

end Laplace.Grammar
