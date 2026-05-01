Use the **kernel split**, and define the bulk term as the **quartic observable remainder block**, not by baking the integrated constants into the definition.

```lean
namespace Laplace.Multi

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Even cross kernel: `(b·u) · (1/6) Φ(u,u,u)`. -/
private noncomputable def crossEvenKernel
    (b : ι → ℝ)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (u : ι → ℝ) : ℝ :=
  dot b u * ((1 / 6 : ℝ) * Φ (fun _ => u))

/-- Odd cross kernel: `(b·u) · ((1/2) quadForm A u - (1/2) tr(A Σ))`. -/
private noncomputable def crossOddKernel
    (A Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ) (u : ι → ℝ) : ℝ :=
  dot b u * ((1 / 2 : ℝ) * quadForm A u - (1 / 2 : ℝ) * trASig A Hinv)

/-- Bulk remainder for Lemma A.

This is the clean version:
`t·√t · (b·u) · R_φ,t(u)` where `R_φ,t = expNumObsRem`.

Equivalently, it is the residual after removing the even kernel
`crossEvenKernel` and the odd centered-quadratic kernel
`√t · crossOddKernel` from
`t·√t · (b·u) · expCovPhiConn`. -/
private noncomputable def bulkErrA
    (φ : (ι → ℝ) → ℝ)
    (b : ι → ℝ)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    (t : ℝ) (u : ι → ℝ) : ℝ :=
  t * Real.sqrt t * dot b u * expNumObsRem φ (0 : ι → ℝ) hφ t u

/-- Symmetrized bulk-A integrand. This is the object you actually bound
locally/tail-wise in the proof of Lemma A. -/
private noncomputable def bulkErrASymmIntegrand
    (V φ : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    (t : ℝ) (u : ι → ℝ) : ℝ :=
  (bulkErrA φ b hφ t u *
      Real.exp (-(rescaledPerturbation V H t u))
    + bulkErrA φ b hφ t (-u) *
      Real.exp (-(rescaledPerturbation V H t (-u))))
    * gaussianWeight H u
```

The key algebraic decomposition is:

```lean
/-- Pointwise decomposition for Lemma A. -/
private lemma cross_linear_connected_pointwise
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    (t : ℝ) (u : ι → ℝ) :
    t * Real.sqrt t * dot b u *
        expCovPhiConn V φ H Hinv (0 : ι → ℝ) hV hφ t u
      = crossEvenKernel b hφ.Φ u
        + Real.sqrt t * crossOddKernel hφ.A Hinv b u
        + bulkErrA φ b hφ t u := by
  unfold bulkErrA crossEvenKernel crossOddKernel
  unfold expCovPhiConn expNumObsRem expNumeratorCoeff
  rw [show Hinv (0 : ι → ℝ) = 0 from map_zero Hinv]
  rw [show dot (0 : ι → ℝ) (tensorContractMatrix hV.T Hinv) = 0 from by
    unfold dot; simp]
  ring
```

Parity facts:

```lean
private lemma crossEvenKernel_even
    (b : ι → ℝ)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (u : ι → ℝ) :
    crossEvenKernel b Φ (-u) = crossEvenKernel b Φ u := by
  unfold crossEvenKernel
  rw [dot_neg, cmm_diag_odd Φ u]
  ring

private lemma crossOddKernel_odd
    (A Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ) (u : ι → ℝ) :
    crossOddKernel A Hinv b (-u) = -crossOddKernel A Hinv b u := by
  unfold crossOddKernel
  rw [dot_neg, quadForm_neg]
  ring

private lemma integral_crossOddKernel_mul_gaussianWeight_eq_zero
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (A Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ) :
    ∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u = 0 := by
  apply integral_odd_mul_gaussian_eq_zero
  intro u
  exact crossOddKernel_odd A Hinv b u
```

The bulk block does **not** have a clean parity by itself; what you use is the
symmetrized integrand:

```lean
private lemma bulkErrA_symmetric
    (V φ : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    {t : ℝ} (ht : 0 < t)
    (h_int : Integrable (fun u : ι → ℝ =>
      bulkErrA φ b hφ t u *
        gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u)))) :
    2 * (∫ u : ι → ℝ,
        bulkErrA φ b hφ t u *
          gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))
      = ∫ u : ι → ℝ, bulkErrASymmIntegrand V φ H b hφ t u := by
  -- same template as `expNumErr₃_symmetric` / `expNumErr₄_symmetric`
  sorry
```

## The three bulk-A bound lemmas

These are the right shapes.

```lean
/-- Local pointwise bound on the symmetrized bulk-A integrand.

Here `ρ` is chosen so that:
- `ρ ≤ hφ.jet_radius`  (observable quartic remainder),
- `ρ ≤ hV.local_radius` (local control on `s_t`),
- `hV.local_const * ρ ≤ hV.coercive_const / 4` (Gaussian absorption). -/
private lemma abs_bulkErrA_local_le
    (V φ : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hρ_le_φjet : ρ ≤ hφ.jet_radius)
    (hρ_le_Vlocal : ρ ≤ hV.local_radius)
    (hρ_decay : hV.local_const * ρ ≤ hV.coercive_const / 4)
    {t : ℝ} (ht1 : 1 ≤ t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ ρ * Real.sqrt t) :
    ∃ K_loc : ℝ, 0 ≤ K_loc ∧
      |bulkErrASymmIntegrand V φ H b hφ t u|
        ≤ K_loc / t *
            (‖u‖ ^ 5 + ‖u‖ ^ 8) *
            Real.exp (-(hV.coercive_const / 4 * ‖u‖ ^ 2)) := by
  -- uses:
  --   bulkErrA = t√t · (b·u) · expNumObsRem
  --   abs_expNumObsRem_local_le
  --   local bounds on `e^{-s_t(u)} - e^{-s_t(-u)}`
  --   Gaussian absorption
  sorry

/-- Tail pointwise bound on the symmetrized bulk-A integrand.

On the tail `ρ√t < ‖u‖`, one gets polynomial growth in `u` times an
extra `exp(-β t)` factor. -/
private lemma abs_bulkErrA_tail_le
    (V φ : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    {ρ : ℝ} (hρ_pos : 0 < ρ) :
    ∃ K_tail : ℝ, ∃ M : ℕ, 0 ≤ K_tail ∧
      ∀ t : ℝ, 1 ≤ t →
      ∀ u : ι → ℝ, ρ * Real.sqrt t < ‖u‖ →
        |bulkErrASymmIntegrand V φ H b hφ t u|
          ≤ K_tail * (1 + ‖u‖ ^ M) *
              Real.exp (-(hV.coercive_const / 2 * ‖u‖ ^ 2)) *
              Real.exp (-(hV.coercive_const * ρ ^ 2 / 2 * t)) := by
  -- uses:
  --   bulkErrA = t√t · (b·u) · expNumObsRem
  --   abs_expNumObsRem_global_le
  --   tail coercive splitting `‖u‖ > ρ√t`
  --   `gaussianWeight * exp(-s_t) ≤ exp(-c‖u‖²)`
  sorry

/-- Integrated `K/t` bound for the bulk-A block. -/
private lemma abs_integral_bulkErrA_le
    (V φ : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ)) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |∫ u : ι → ℝ,
          bulkErrA φ b hφ t u *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u))|
        ≤ K / t := by
  -- proof pattern:
  --   1. choose ρ as usual;
  --   2. symmetrize via `bulkErrA_symmetric`;
  --   3. split local / tail with the two pointwise bounds above;
  --   4. integrate against Gaussian-poly envelopes.
  sorry
```

## The two transport blocks that sit beside `bulkErrA`

These are the two other components you want in the final Lemma A proof.

```lean
/-- Even block: `(b·u) · (1/6) Φ_φ(u,u,u)` transports with coefficient
`(1/2)·dot (Σb) (Φ_φ : Σ)`. -/
private theorem rescaledIntegral_evenCross_asymptotic
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |(∫ u : ι → ℝ,
          crossEvenKernel b hφ.Φ u *
            gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))
        - ((1 / 2 : ℝ) *
            dot (Hinv b) (tensorContractMatrix hφ.Φ Hinv)) *
            rescaledPartition V t|
        ≤ K / t := by
  sorry

/-- Odd block: `√t · ∫ (b·u)·Q^c_φ(u) · gW · e^{-s_t}` transports with the
two `T`-contraction coefficients coming from
`gaussian_centeredQuad_linear_cubic_explicit`. -/
private theorem rescaledIntegral_oddCross_asymptotic
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hφ : ObservableTensorApprox φ (0 : ι → ℝ))
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |Real.sqrt t *
          (∫ u : ι → ℝ,
              crossOddKernel hφ.A Hinv b u *
                gaussianWeight H u *
                Real.exp (-(rescaledPerturbation V H t u)))
        + ((1 / 2 : ℝ) * dot b
              (Hinv (hφ.A (Hinv (tensorContractMatrix hV.T Hinv))))
          + (1 / 2 : ℝ) * dot (Hinv b)
              (tensorContractMatrix hV.T (Hinv.comp (hφ.A.comp Hinv))))
            * rescaledPartition V t|
        ≤ K / t := by
  -- split `√t (e^{-s_t} - 1) = - (1/6) T + corrected`
  -- main term via `gaussian_centeredQuad_linear_cubic_explicit`
  sorry
```

## Lemma A architecture

Use the pointwise decomposition:

```lean
t * Real.sqrt t * dot b u * expCovPhiConn ...
  = crossEvenKernel b hφ.Φ u
    + Real.sqrt t * crossOddKernel hφ.A Hinv b u
    + bulkErrA φ b hφ t u
```

Then integrate against `gaussianWeight H u * exp(-rescaledPerturbation ...)`:

1. **Even block**
   - main Gaussian term via `gaussian_cubic_linear`;
   - correction `O(1/t)` via `rescaledIntegral_evenCross_asymptotic`.

2. **Odd block**
   - `∫ crossOddKernel * gW = 0` by parity;
   - write
     ```lean
     Real.sqrt t * ∫ crossOddKernel * gW * exp(-s_t)
       = - ∫ crossOddKernel * ((1 / 6) * hV.T (fun _ => u)) * gW
         + Real.sqrt t * ∫ crossOddKernel * gW *
             (Real.exp (-s_t) - 1 + expPotCubic V H hV.toPotentialTensorApprox t u)
     ```
   - main term from `gaussian_centeredQuad_linear_cubic_explicit`;
   - corrected-bracket remainder `O(1/t)`.

3. **Bulk block**
   - `bulkErrA = t√t · (b·u) · expNumObsRem`;
   - use `bulkErrA_symmetric`;
   - local + tail estimates above;
   - conclude with `abs_integral_bulkErrA_le`.

4. **Final assembly**
   - triangle inequality over the three blocks;
   - constants combine to the exact coefficient in
     `rescaledIntegral_cross_linear_connected_asymptotic`.

If you want, I can next write the **exact theorem header + pointwise decomposition proof** for `rescaledIntegral_cross_linear_connected_asymptotic`, already wired to these names.