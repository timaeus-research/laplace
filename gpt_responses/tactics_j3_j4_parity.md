Short tactical answer: **don’t** factor a fully generic “odd Gaussian against symmetric perturbation” helper. In this file, the reusable part is just the **`u ↦ -u` substitution** plus the even/odd identities of the pieces. After that, inline the local/tail argument separately for `J₃` and `J₄`.

Below are the bits I would actually paste.

```lean
private lemma integral_comp_neg_pi
    (f : (ι → ℝ) → ℝ) :
    ∫ u : ι → ℝ, f (-u) = ∫ u : ι → ℝ, f u := by
  simpa using
    (measurePreserving_neg_pi (ι := ι)).integral_comp
      (fun u : ι → ℝ => f u)

private lemma expNumLin_neg
    (a : ι → ℝ) (t : ℝ) (u : ι → ℝ) :
    expNumLin a t (-u) = - expNumLin a t u := by
  simp [expNumLin, dot]

private lemma expNumQuad_neg
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    (hφ : ObservableTensorApprox φ a) (t : ℝ) (u : ι → ℝ) :
    expNumQuad φ a hφ t (-u) = expNumQuad φ a hφ t u := by
  simp [expNumQuad, quadForm]

private lemma expPotCubic_neg
    (V : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H)
    (t : ℝ) (u : ι → ℝ) :
    expPotCubic V H hV t (-u) = - expPotCubic V H hV t u := by
  simp [expPotCubic, cmm_diag_odd]

private lemma expNumErr₄_neg_eq
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (t : ℝ) :
    expNumErr₄ V φ a H Hinv hV hφ t
      =
      ∫ u : ι → ℝ,
        (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
          (Real.exp (-(rescaledPerturbation V H t (-u))) - 1) *
          gaussianWeight H u := by
  rw [expNumErr₄]
  symm
  simpa [expNumQuad_neg, gaussianWeight_neg]
    using
      (integral_comp_neg_pi
        (fun u : ι → ℝ =>
          (expNumQuad φ a hφ t u - expNumeratorCoeff V φ H Hinv a hV hφ / t) *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1) *
            gaussianWeight H u))

private lemma expNumErr₃_neg_eq
    (V : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (t : ℝ) :
    expNumErr₃ V H hV a t
      =
      ∫ u : ι → ℝ,
        (- expNumLin a t u) *
          (Real.exp (-(rescaledPerturbation V H t (-u))) - 1 +
            expPotCubic V H hV t (-u)) *
          gaussianWeight H u := by
  rw [expNumErr₃]
  symm
  simpa [expNumLin_neg, gaussianWeight_neg]
    using
      (integral_comp_neg_pi
        (fun u : ι → ℝ =>
          expNumLin a t u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
              expPotCubic V H hV t u) *
            gaussianWeight H u))
```

## What closes and what doesn’t

### `J₄`
This symmetrization is enough:
\[
J₄ = \frac12 \int B_t(u)\,\bigl[(e^{-s_t(u)}-1)+(e^{-s_t(-u)}-1)\bigr]\,g(u)\,du
\]
with `B_t(-u)=B_t(u)`.

Then the local bracket estimate is the one you want to feed into the same local/tail wrapper as `expNumErr₁_bound`:

```lean
have hpair :
    |(Real.exp (-(rescaledPerturbation V H t u)) - 1) +
      (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)|
      ≤
      |Real.exp (-(rescaledPerturbation V H t u)) -
          (1 - rescaledPerturbation V H t u)| +
      |Real.exp (-(rescaledPerturbation V H t (-u))) -
          (1 - rescaledPerturbation V H t (-u))| +
      |rescaledPerturbation V H t u + rescaledPerturbation V H t (-u)| := by
  have : (Real.exp (-(rescaledPerturbation V H t u)) - 1) +
      (Real.exp (-(rescaledPerturbation V H t (-u))) - 1)
      =
      (Real.exp (-(rescaledPerturbation V H t u)) -
          (1 - rescaledPerturbation V H t u)) +
      (Real.exp (-(rescaledPerturbation V H t (-u))) -
          (1 - rescaledPerturbation V H t (-u))) -
      (rescaledPerturbation V H t u + rescaledPerturbation V H t (-u)) := by
    ring
  rw [this]
  nlinarith [abs_add
    (Real.exp (-(rescaledPerturbation V H t u)) -
      (1 - rescaledPerturbation V H t u))
    ((Real.exp (-(rescaledPerturbation V H t (-u))) -
      (1 - rescaledPerturbation V H t (-u))) -
      (rescaledPerturbation V H t u + rescaledPerturbation V H t (-u))),
    abs_add
      (Real.exp (-(rescaledPerturbation V H t (-u))) -
        (1 - rescaledPerturbation V H t (-u)))
      (-(rescaledPerturbation V H t u + rescaledPerturbation V H t (-u)))]
```

Then use `abs_exp_neg_sub_one_add_le` on each exponential term and the local estimate
`|s_t(u)+s_t(-u)| ≤ C * ‖u‖^4 / t`
(from `abs_rescaledPerturbation_sub_scaledCubicJet_le` plus oddness of `expPotCubic`).

### `J₃`
Here is the important point: **with only the hypotheses you pasted, `J₃` does not close**.  
After symmetrization you still need an **odd-part remainder bound**
\[
|(s_t(u)-C_t(u))-(s_t(-u)-C_t(-u))| \lesssim \|u\|^5/t^{3/2}
\]
(or an equivalent estimate on `s_t(u)-s_t(-u)-2 C_t(u)`).

Without that, the local term only gives `O(t^{-3/2})`.

So my recommendation is:

- **Inline** the substitution for both lemmas using the snippets above.
- Finish `J₄` with your existing `expNumErr₁_bound` local/tail boilerplate.
- For `J₃`, first prove the odd-remainder local lemma; then the rest is the same boilerplate.

If you want, send the local/tail wrapper you used in `expNumErr₁_bound`; I can then write the final pasteable `expNumErr₄_bound` in your exact style.