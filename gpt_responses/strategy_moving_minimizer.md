Your block-inverse argument is correct. For a curve parametrised by the **original** coordinate `s`, it is a direct route; the kernel-coordinate implicit-function API does not automatically save work. I would not claim it is universally the lightest route.

**Qualification:** I cannot inspect/run the v4.33.0 pin here. Below is a concrete proof skeleton, not a certified compiling file; in particular I cannot certify the argument order of `equivOfInverse` or its named simp lemmas.

### API checks

Run these against the pin:

```lean
import Mathlib

#check HasStrictFDerivAt.localInverse
#check HasStrictFDerivAt.to_localInverse
#check HasStrictFDerivAt.localInverse_apply_image
#check HasStrictFDerivAt.eventually_right_inverse
#check ContinuousLinearEquiv.equivOfInverse
#check LinearMap.toContinuousLinearMap
#check HasDerivAt.snd
#check HasDerivAt.prodMk
#check hasStrictFDerivAt_fst
#check HasStrictFDerivAt.prodMk
#check HasStrictFDerivAt.congr_fderiv
#check HasFDerivAt.comp_hasDerivAt
```

The inverse-function statements needed have these mathematical types, with `I := hΦ.localInverse Φ P a`:

```lean
-- localInverse_apply_image : I (Φ a) = a
-- eventually_right_inverse : ∀ᶠ q in 𝓝 (Φ a), Φ (I q) = q
-- to_localInverse :
--   HasStrictFDerivAt I (P.symm : _ →L[ℝ] _) (Φ a)
```

### Skeleton

Under your hypotheses, including `hz : G 0 w₀ = 0`:

```lean
open Filter
open scoped Topology Matrix

-- E := ι → ℝ
let Φ : ℝ × E → ℝ × E := fun p => (p.1, G p.1 p.2)
let D := (ContinuousLinearMap.fst ℝ ℝ E).prod G'

have block :
    ∃ P : (ℝ × E) ≃L[ℝ] (ℝ × E),
      (P : (ℝ × E) →L[ℝ] (ℝ × E)) = D ∧
      ∀ σ y, P.symm (σ, y) =
        (σ, H⁻¹ *ᵥ (y - σ • g)) := by
  -- Construct inverse CLM B as described below.
  -- Prove D.comp B = id and B.comp D = id by extensionality,
  -- hG', and the two nonsingular-matrix inverse identities.
  -- Package using equivOfInverse; inverse evaluation should reduce
  -- definitionally, so named apply/symm_apply lemmas are unnecessary.
  sorry

obtain ⟨P, hP, hPinv⟩ := block

have hΦ : HasStrictFDerivAt Φ (P : _ →L[ℝ] _) (0, w₀) := by
  rw [hP]
  exact (hasStrictFDerivAt_fst (0, w₀)).prodMk hGs

have hbase : Φ (0, w₀) = (0, 0) := by simp [Φ, hz]

let I := hΦ.localInverse Φ P (0, w₀)
let w : ℝ → E := fun s => (I (s, 0)).2

have hw0 : w 0 = w₀ := by
  have hi : I (0, 0) = (0, w₀) := by
    simpa only [hbase] using hΦ.localInverse_apply_image
  exact congrArg Prod.snd hi

have hline : HasDerivAt (fun s : ℝ => (s, (0 : E))) (1, 0) 0 :=
  (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 (0 : E))

have hroot : ∀ᶠ s in 𝓝 0, G s (w s) = 0 := by
  have hr : ∀ᶠ q in 𝓝 ((0 : ℝ), (0 : E)), Φ (I q) = q := by
    simpa only [hbase] using hΦ.eventually_right_inverse
  filter_upwards [hline.continuousAt.tendsto.eventually hr] with s hs
  have hf : (I (s, 0)).1 = s := congrArg Prod.fst hs
  have hg : G (I (s, 0)).1 (I (s, 0)).2 = 0 :=
    congrArg Prod.snd hs
  simpa only [hf] using hg

have hI : HasFDerivAt I (P.symm : _ →L[ℝ] _) (0, 0) := by
  simpa only [hbase] using hΦ.to_localInverse.hasFDerivAt

have hw' : HasDerivAt w (-(H⁻¹ *ᵥ g)) 0 := by
  simpa [w, hPinv] using (hI.comp_hasDerivAt 0 hline).snd

exact ⟨w, hw0, hroot, hw'⟩
```

For the missing block, only convert `Matrix.toLin' H⁻¹` to a CLM; build the remaining inverse using CLM `fst`, `snd`, `smulRight`, subtraction, composition, and `prod`.

Completeness and finite-dimensional continuity instances are automatic here. The Pi sup norm causes no problem. Explicitly retain the coercion `(P : _ →L[ℝ] _)`.

Finally, **“moving minimiser” requires extra hypotheses**: invertible Hessian plus stationarity yields a stationary branch, not necessarily a minimising branch.