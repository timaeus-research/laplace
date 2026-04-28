Short answers first:

1. **Direct vs reuse**: do **(a) direct**, but only factor **four tiny EXP-specific helpers**. Don’t genericize `CovarianceSharp.lean` yet; the algebra is different enough that the abstraction cost is not worth it.

2. **Glocal+Gtail reuse**: reuse the **pointwise Stage 1/2 bounds** and the Gaussian-integrability bookkeeping, but you probably need **new EXP wrappers**. The COV helpers are too tied to the `φ·ψ` product decomposition.

3. **Correct EXP decomposition**: use **4 terms**, not 3, if you want clean `O(t⁻²)` bounds:
   \[
   N_t - D_t \frac{\mu}{t}=J_1+J_2+J_3+J_4
   \]
   with
   - \(J_1=\int R_{\phi,t}\,e^{-s_t}g_W\)
   - \(J_2=\int P_{\phi,t}(e^{-s_t}-1)g_W\)
   - \(J_3=\int L_t(e^{-s_t}-1+C_t)g_W\)
   - \(J_4=\int (Q_t-\mu/t)(e^{-s_t}-1)g_W\)

   where
   - \(L_t=(1/\sqrt t)\,\langle a,u\rangle\)
   - \(Q_t=(1/t)\,(1/2)\,u^TAu\)
   - \(P_{\phi,t}=(1/t^{3/2})(1/6)\Phi(u,u,u)\)
   - \(C_t=(1/\sqrt t)(1/6)T(u,u,u)\)
   - \(R_{\phi,t}=\phi((\sqrt t)^{-1}u)-L_t-Q_t-P_{\phi,t}\)
   - \(\mu=(\operatorname{tr}(A\Sigma)-\langle \Sigma a,T{:}\Sigma\rangle)/2\).

   Then the Gaussian main term cancels exactly:
   \[
   \int(-L_t-Q_t-P_{\phi,t}+L_tC_t+\mu/t)\,g_W=0.
   \]

Below is the skeleton I would paste. The **main theorem proof is complete modulo four helper lemmas + one decomposition lemma**. Those helpers are exactly the four blocks above and are the right place to copy/adapt the COV sharp proofs.

```lean
/-
  EXP sharp centered numerator helper.

  Strategy:
  * define the coefficient μ
  * decompose the centered numerator into four error terms
  * prove each error term is O(t^-2)
  * combine by triangle inequality

  Notes:
  * You will almost certainly only need to edit the names of your existing
    Gaussian rewrite / perturbation lemmas.
  * The two genuinely new estimates are the J₃/J₄ parity-symmetrized bounds.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Real

namespace LaplaceAsymptotics

variable {ι : Type*}
variable [Nonempty ι]

/-- The explicit first-order coefficient in the EXP numerator. -/
private def expNumeratorCoeff
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)) : ℝ :=
  (trASig hφ.A Hinv - dot (Hinv a) (tensorContractMatrix hV.T Hinv)) / 2

/-- Scaled linear jet of `φ((√t)⁻¹ • u)`. -/
private def expNumLin
    (a : ι → ℝ) (t : ℝ) (u : ι → ℝ) : ℝ :=
  (Real.sqrt t)⁻¹ * dot a u

/-- Scaled quadratic jet of `φ((√t)⁻¹ • u)`. -/
private def expNumQuad
    (hφ : ObservableTensorApprox φ a) (t : ℝ) (u : ι → ℝ) : ℝ :=
  (1 / t) * ((1 / 2 : ℝ) * quadForm hφ.A u)

/-- Scaled cubic jet of `φ((√t)⁻¹ • u)`. -/
private def expNumCubic
    (hφ : ObservableTensorApprox φ a) (t : ℝ) (u : ι → ℝ) : ℝ :=
  ((Real.sqrt t)⁻¹ / t) * ((1 / 6 : ℝ) * hφ.Φ (fun _ => u))

/-- Scaled cubic jet of the potential perturbation. -/
private def expPotCubic
    (hV : PotentialTensorApprox V H) (t : ℝ) (u : ι → ℝ) : ℝ :=
  (Real.sqrt t)⁻¹ * ((1 / 6 : ℝ) * hV.T (fun _ => u))

/-- Quartic-and-higher observable remainder. -/
private def expNumObsRem
    (φ : (ι → ℝ) → ℝ)
    (hφ : ObservableTensorApprox φ a)
    (t : ℝ) (u : ι → ℝ) : ℝ :=
  φ ((Real.sqrt t)⁻¹ • u)
    - expNumLin a t u
    - expNumQuad hφ t u
    - expNumCubic hφ t u

/-
  IMPORTANT:
  replace `rescaledPerturbation V H t u` below by your actual rescaled
  perturbation function name if needed.
-/

/-- Error term J₁: quartic observable remainder against the full Gibbs factor. -/
private def expNumErr₁
    (V φ : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hφ : ObservableTensorApprox φ a)
    (t : ℝ) : ℝ :=
  ∫ u, expNumObsRem φ hφ t u
      * Real.exp (-(rescaledPerturbation V H t u))
      * Real.exp (-(1 / 2 : ℝ) * quadForm H u)

/-- Error term J₂: cubic observable jet against `(e^{-s_t} - 1)`. -/
private def expNumErr₂
    (V φ : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hφ : ObservableTensorApprox φ a)
    (t : ℝ) : ℝ :=
  ∫ u, expNumCubic hφ t u
      * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
      * Real.exp (-(1 / 2 : ℝ) * quadForm H u)

/-- Error term J₃: linear observable jet against the odd remainder. -/
private def expNumErr₃
    (V : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H)
    (a : ι → ℝ)
    (t : ℝ) : ℝ :=
  ∫ u, expNumLin a t u
      * (Real.exp (-(rescaledPerturbation V H t u)) - 1 + expPotCubic hV t u)
      * Real.exp (-(1 / 2 : ℝ) * quadForm H u)

/-- Error term J₄: centered quadratic observable jet against `(e^{-s_t} - 1)`. -/
private def expNumErr₄
    (V φ : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (t : ℝ) : ℝ :=
  ∫ u, (expNumQuad hφ t u - expNumeratorCoeff hV hφ Hinv / t)
      * (Real.exp (-(rescaledPerturbation V H t u)) - 1)
      * Real.exp (-(1 / 2 : ℝ) * quadForm H u)

/-
  === Core exact decomposition ===

  This is the EXP analogue of your `pair_product_expansion`.
  Proof recipe:
  * rewrite `rescaledNumerator` and `rescaledPartition` into Gaussian form
  * expand the integrand
  * split into J₁+J₂+J₃+J₄ plus Gaussian main terms
  * kill the Gaussian main terms by:
      - oddness of the linear and cubic observable jets
      - `gaussian_quad_expectation`
      - `gaussian_linear_cubic`
-/
lemma expNumerator_centered_decomp
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCovHypotheses H Hinv)
    {t : ℝ} (ht : 0 < t) :
    rescaledNumerator V t φ
      - rescaledPartition V t * (expNumeratorCoeff hV hφ Hinv / t)
      =
      expNumErr₁ V φ H hφ t
      + expNumErr₂ V φ H hφ t
      + expNumErr₃ V H hV a t
      + expNumErr₄ V φ H Hinv hV hφ t := by
  /-
    Copy the proof pattern of `pair_product_expansion`, with these replacements:

    φψ-product main block  ->  `expNumObsRem + expNumCubic + expNumLin + expNumQuad`
    cubic potential block  ->  `expPotCubic`
    covariance centering   ->  scalar centering by `expNumeratorCoeff`

    The Gaussian cancellation is:
      ∫ (-L_t - Q_t - P_t + L_t*C_t + μ/t) gW = 0
    where:
      * `∫ L_t gW = 0`              (odd)
      * `∫ P_t gW = 0`              (odd)
      * `∫ Q_t gW = Z * trASig(...) / (2t)` by `gaussian_quad_expectation`
      * `∫ L_t*C_t gW = Z * dot(...) / (2t)` by `gaussian_linear_cubic`
  -/
  sorry

/-
  === Four O(t^-2) bounds ===

  J₁: straight observable quartic remainder, same style as the easy COV remainder.
-/
lemma expNumErr₁_bound
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |expNumErr₁ V φ H hφ t| ≤ K / t^2 := by
  /-
    Copy the “observable jet remainder × full Gibbs factor” helper from the COV
    proof. This is the easiest one: just use `hφ.Φ_jet_bound` rescaled.
  -/
  sorry

/-
  J₂: cubic observable jet × `(e^{-s_t} - 1)`.
  Since `expNumCubic = O(t^{-3/2} ‖u‖^3)` and `e^{-s_t} - 1 = O(t^{-1/2} ‖u‖^3)`,
  this is directly O(t^-2) by absolute values.
-/
lemma expNumErr₂_bound
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |expNumErr₂ V φ H hφ t| ≤ K / t^2 := by
  /-
    Reuse the Stage-1/Stage-2 perturbation bounds exactly as in the COV proof.
  -/
  sorry

/-
  J₃: linear jet × odd remainder.

  DO NOT bound `|e^{-s_t} - 1 + C_t|` crudely; that only gives O(t^-3/2).
  First symmetrize under `u ↦ -u` so only the odd part survives:
    J₃ = (1/2) ∫ L_t(u) * [R(u) - R(-u)] * gW(u) du
  with `R(u) = e^{-s_t(u)} - 1 + C_t(u)`.
  Then `R(u) - R(-u)` is O(t^-3/2), hence J₃ = O(t^-2).
-/
lemma expNumErr₃_bound
    (V : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    (hV : PotentialTensorApprox V H)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |expNumErr₃ V H hV a t| ≤ K / t^2 := by
  /-
    New EXP-specific helper.
    Proof = your COV odd-slot proof with one observable removed.
  -/
  sorry

/-
  J₄: centered quadratic jet × `(e^{-s_t} - 1)`.

  Again, use parity first:
    J₄ = (1/2) ∫ (Q_t(u)-μ/t) * [(e^{-s_t(u)}-1) + (e^{-s_t(-u)}-1)] * gW(u) du
  The bracket is the even part, hence O(t^-1), so J₄ = O(t^-2).
-/
lemma expNumErr₄_bound
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |expNumErr₄ V φ H Hinv hV hφ t| ≤ K / t^2 := by
  /-
    New EXP-specific helper.
    Proof = your COV even-slot proof with the pair-product block removed.
  -/
  sorry

theorem rescaledNumerator_first_order_centered_explicit
    (V φ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    (hφ : ObservableTensorApprox φ a)
    (hGauss : LaplaceCovHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |rescaledNumerator V t φ
        - rescaledPartition V t *
            ((trASig hφ.A Hinv
              - dot (Hinv a) (tensorContractMatrix hV.T Hinv)) / (2 * t))|
        ≤ K / t^2 := by
  let μ : ℝ := expNumeratorCoeff hV hφ Hinv

  obtain ⟨K₁, T₁, hT₁, h₁⟩ :=
    expNumErr₁_bound (V := V) (φ := φ) (H := H) (Hinv := Hinv)
      (a := a) hV hφ hGauss
  obtain ⟨K₂, T₂, hT₂, h₂⟩ :=
    expNumErr₂_bound (V := V) (φ := φ) (H := H) (Hinv := Hinv)
      (a := a) hV hφ hGauss
  obtain ⟨K₃, T₃, hT₃, h₃⟩ :=
    expNumErr₃_bound (V := V) (H := H) (Hinv := Hinv)
      (a := a) hV hGauss
  obtain ⟨K₄, T₄, hT₄, h₄⟩ :=
    expNumErr₄_bound (V := V) (φ := φ) (H := H) (Hinv := Hinv)
      (a := a) hV hφ hGauss

  refine ⟨K₁ + K₂ + K₃ + K₄, max (max (max T₁ T₂) (max T₃ T₄)) 1, ?_, ?_⟩
  · exact le_max_right _ _
  · intro t ht
    have ht1 : T₁ ≤ t := le_trans (by
      exact le_trans (le_max_left _ _) (le_max_left _ _)) ht
    have ht2 : T₂ ≤ t := le_trans (by
      exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) ht
    have ht3 : T₃ ≤ t := le_trans (by
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) ht
    have ht4 : T₄ ≤ t := le_trans (by
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) ht
    have h1' : 1 ≤ t := le_trans (le_max_right _ _) ht
    have ht_pos : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h1'

    have hdecomp :=
      expNumerator_centered_decomp
        (V := V) (φ := φ) (H := H) (Hinv := Hinv)
        (a := a) hV hφ hGauss ht_pos

    have hsum :
        |expNumErr₁ V φ H hφ t
          + expNumErr₂ V φ H hφ t
          + expNumErr₃ V H hV a t
          + expNumErr₄ V φ H Hinv hV hφ t|
        ≤ |expNumErr₁ V φ H hφ t|
          + |expNumErr₂ V φ H hφ t|
          + |expNumErr₃ V H hV a t|
          + |expNumErr₄ V φ H Hinv hV hφ t| := by
      calc
        |(expNumErr₁ V φ H hφ t + expNumErr₂ V φ H hφ t)
          + (expNumErr₃ V H hV a t + expNumErr₄ V φ H Hinv hV hφ t)| ≤
            |expNumErr₁ V φ H hφ t + expNumErr₂ V φ H hφ t|
            + |expNumErr₃ V H hV a t + expNumErr₄ V φ H Hinv hV hφ t| := abs_add _ _
        _ ≤ (|expNumErr₁ V φ H hφ t| + |expNumErr₂ V φ H hφ t|)
            + (|expNumErr₃ V H hV a t| + |expNumErr₄ V φ H Hinv hV hφ t|) := by
              gcongr <;> exact abs_add _ _
        _ = _ := by ring

    have hK1 := h₁ t ht1
    have hK2 := h₂ t ht2
    have hK3 := h₃ t ht3
    have hK4 := h₄ t ht4

    rw [hdecomp]
    have : |expNumErr₁ V φ H hφ t
          + expNumErr₂ V φ H hφ t
          + expNumErr₃ V H hV a t
          + expNumErr₄ V φ H Hinv hV hφ t|
        ≤ (K₁ + K₂ + K₃ + K₄) / t^2 := by
      have ht_sq_pos : 0 < t^2 := sq_pos_of_pos ht_pos
      nlinarith [hsum, hK1, hK2, hK3, hK4]
    simpa [μ, expNumeratorCoeff, two_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using this

end LaplaceAsymptotics
```

### What to actually implement next
- `expNumerator_centered_decomp`
- `expNumErr₁_bound`
- `expNumErr₂_bound`
- `expNumErr₃_bound` (new parity helper)
- `expNumErr₄_bound` (new parity helper)

If you want, I can next write the **exact Lean proof for `expNumerator_centered_decomp`** in the style of your existing `pair_product_expansion`, which is the key algebraic step.