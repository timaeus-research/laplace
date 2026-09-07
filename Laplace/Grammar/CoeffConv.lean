/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.FamilyTaylorTree
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Data.Pi.Interval

/-!
# Convolution of coefficient families (Stage 5a)

Unit 251 (Taylor-tree programme; Astra #29 candidate A, first unit). The Cauchy product of two
coefficient families on multi-indices,
```
(c * e)_γ = ∑_{α ≤ γ} c_α e_{γ-α}       (`CoeffFamily.conv`, a finite sum over `Finset.Iic γ`),
```
is the coefficient family of the product of the represented functions: on the closed cube
`evalF (conv c e) u = evalF c u · evalF e u` (`evalF_conv`), and it is absolutely summable with
`mass (conv c e) ≤ mass c · mass e` (`mass_conv_le`). The proof regroups the absolutely convergent
double series over pairs `(α, δ)` along `γ = α + δ` through the equivalence
`(α, δ) ↦ ⟨α + δ, α⟩` (`pairEquiv`) and `HasSum.sigma`; no global antidiagonal instance is needed.
The
paper's Taylor coefficients `ξ_{n,p}` of `(ξ − ξ(0))^p` (eq:flucttreeterms) are the iterated
convolution `J^{*p}`. No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open MonoRep

namespace CoeffFamily

variable {d : ℕ}

/-- Pairs `(α, δ)` of multi-indices ↔ `⟨γ, α⟩` with `α ≤ γ`, via `γ = α + δ`. -/
def pairEquiv (d : ℕ) :
    (Fin d → ℕ) × (Fin d → ℕ) ≃ Σ γ : Fin d → ℕ, ↥(Finset.Iic γ) where
  toFun p := ⟨p.1 + p.2, ⟨p.1, Finset.mem_Iic.2 fun i => Nat.le_add_right _ _⟩⟩
  invFun s := (s.2.1, s.1 - s.2.1)
  left_inv p := Prod.ext rfl (funext fun i => by simp)
  right_inv s := Sigma.subtype_ext (add_tsub_cancel_of_le (Finset.mem_Iic.1 s.2.2)) rfl

/-- The Cauchy product `(c * e)_γ = ∑_{α ≤ γ} c_α e_{γ-α}`. -/
noncomputable def conv (c e : CoeffFamily d) : CoeffFamily d :=
  fun γ => ∑ α ∈ Finset.Iic γ, c α * e (γ - α)

/-- The double series over pairs, regrouped along `γ = α + δ`. -/
theorem hasSum_conv_mono {c e : CoeffFamily d} (hc : AbsSummable c) (he : AbsSummable e)
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    HasSum (fun γ => conv c e γ * mono γ u) (evalF c u * evalF e u) := by
  have hcs := summable_abs_term hc hu
  have hes := summable_abs_term he hu
  have hcs' : Summable fun γ => ‖c γ * mono γ u‖ := by simpa [Real.norm_eq_abs] using hcs
  have hes' : Summable fun γ => ‖e γ * mono γ u‖ := by simpa [Real.norm_eq_abs] using hes
  have hpair : HasSum (fun p : (Fin d → ℕ) × (Fin d → ℕ) =>
      (c p.1 * mono p.1 u) * (e p.2 * mono p.2 u)) (evalF c u * evalF e u) := by
    have hs := summable_mul_of_summable_norm hcs' hes'
    have := hs.hasSum
    rwa [← tsum_mul_tsum_of_summable_norm hcs' hes'] at this
  -- transport to the sigma type
  set F : (Σ γ : Fin d → ℕ, ↥(Finset.Iic γ)) → ℝ :=
    fun s => c s.2.1 * e (s.1 - s.2.1) * mono s.1 u with hF
  have hFe : ∀ p, F (pairEquiv d p) = (c p.1 * mono p.1 u) * (e p.2 * mono p.2 u) := by
    intro p
    simp only [hF, pairEquiv, Equiv.coe_fn_mk, add_tsub_cancel_left, mono_add]
    ring
  have hFsum : HasSum F (evalF c u * evalF e u) := by
    rw [← (pairEquiv d).hasSum_iff]
    exact hpair.congr_fun fun p => (hFe p).symm ▸ rfl
  refine hFsum.sigma fun γ => ?_
  -- the fibre over `γ` is the finite sum over `Iic γ`
  have : ∑ α : ↥(Finset.Iic γ), F ⟨γ, α⟩ = conv c e γ * mono γ u := by
    unfold conv
    rw [Finset.sum_mul, ← Finset.sum_coe_sort (Finset.Iic γ) (fun α => c α * e (γ - α) * mono γ u)]
  rw [← this]
  exact hasSum_fintype _

/-- **`evalF (conv c e) = evalF c · evalF e`** on the closed cube. -/
theorem evalF_conv {c e : CoeffFamily d} (hc : AbsSummable c) (he : AbsSummable e)
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    evalF (conv c e) u = evalF c u * evalF e u :=
  (hasSum_conv_mono hc he hu).tsum_eq

theorem one_mem_closedCube (d : ℕ) : (fun _ => (1 : ℝ)) ∈ closedCube d :=
  fun _ _ => ⟨zero_le_one, le_rfl⟩

theorem mono_one (γ : Fin d → ℕ) : mono γ (fun _ => (1 : ℝ)) = 1 := by
  unfold mono; simp

/-- The absolute family `|c|` is absolutely summable with the same mass. -/
theorem absFamily_summable {c : CoeffFamily d} (hc : AbsSummable c) :
    AbsSummable fun γ => |c γ| := by
  unfold AbsSummable at hc ⊢
  simpa [abs_abs] using hc

theorem evalF_absFamily_one {c : CoeffFamily d} : evalF (fun γ => |c γ|) (fun _ => 1) = mass c := by
  unfold evalF mass
  simp [mono_one]

theorem abs_conv_le (c e : CoeffFamily d) (γ : Fin d → ℕ) :
    |conv c e γ| ≤ conv (fun γ => |c γ|) (fun γ => |e γ|) γ := by
  unfold conv
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun α _ => abs_mul _ _

/-- The convolution of absolutely summable families is absolutely summable. -/
theorem AbsSummable.conv {c e : CoeffFamily d} (hc : AbsSummable c) (he : AbsSummable e) :
    AbsSummable (conv c e) := by
  have h := hasSum_conv_mono (absFamily_summable hc) (absFamily_summable he) (one_mem_closedCube d)
  simp only [mono_one, mul_one] at h
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_conv_le c e) h.summable

/-- **`mass (conv c e) ≤ mass c · mass e`.** -/
theorem mass_conv_le {c e : CoeffFamily d} (hc : AbsSummable c) (he : AbsSummable e) :
    mass (conv c e) ≤ mass c * mass e := by
  have h := hasSum_conv_mono (absFamily_summable hc) (absFamily_summable he) (one_mem_closedCube d)
  simp only [mono_one, mul_one, evalF_absFamily_one] at h
  change ∑' γ, |conv c e γ| ≤ mass c * mass e
  rw [← h.tsum_eq]
  exact Summable.tsum_le_tsum (abs_conv_le c e) (hc.conv he) h.summable

end CoeffFamily

end Laplace.Grammar
