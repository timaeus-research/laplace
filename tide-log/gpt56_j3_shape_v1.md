## 1. Symmetry regularity fork

### Recommendation: choose (c), with an analytic/smooth convenience wrapper

Make the load-bearing J3 theorem purely algebraic:

```lean
def ContinuousMultilinearMap.IsSymm
    (A : E [×k]→L[ℝ] F) : Prop :=
  ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E),
    A (fun i => v (σ i)) = A v
```

and prove polarization from this hypothesis. Then add a corollary for iterated derivatives whose symmetry is obtained from:

```lean
ContDiffAt.iteratedFDeriv_comp_perm
```

This separation is preferable because:

1. Polarization is an algebraic fact and should not depend on how symmetry was obtained.
2. It isolates the unstable part of the Mathlib API—the exact statement and orientation of `iteratedFDeriv_comp_perm`.
3. It permits later use with hand-constructed tensors or with a future finite-regularity Schwarz theorem.
4. It keeps the downstream J6 theorem simple.

I recommend the pointwise symmetry predicate over exposing `domDomCongr` in the public statement. It is easier to apply and less sensitive to API orientation.

### Important terminology caveat

`ContDiff ℝ ω f` is smooth/\(C^\infty\), not Mathlib's assertion that `f` is real analytic. Analyticity implies the needed smoothness, but `ContDiff ℝ ω` itself does not encode convergence of a Taylor series.

### Why not prove the \(C^k\) symmetry theorem now?

Option (b) is mathematically standard but likely a substantial Mathlib project. The expected induction is:

1. Prove invariance under adjacent transpositions.
2. Express the \(k\)-th derivative as the derivative of the \((k-2)\)-th derivative.
3. Apply `second_derivative_symmetric` or `isSymmSndFDerivAt` to the last two directions.
4. Transport this through the currying/reassociation representation of iterated continuous multilinear maps.
5. Show adjacent transpositions generate every permutation.

The difficult Lean work is not the mathematics but:

- regularity bookkeeping after taking derivatives;
- converting between curried and uncurried continuous multilinear maps;
- matching the representation used by `iteratedFDeriv`;
- composing adjacent-transposition invariance into arbitrary permutation invariance.

This is likely much more work than J3 itself. It should be a separate library contribution, not a prerequisite for polarization.

---

## 2. Subset-sum polarization in Lean

### Suggested statements

First prove the identity itself:

```lean
theorem ContinuousMultilinearMap.factorial_smul_eq_sum_diag
    (A : E [×k]→L[ℝ] F)
    (hA : A.IsSymm)
    (v : Fin k → E) :
    (k.factorial : ℝ) • A v =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        ((-1 : ℝ) ^ (k - S.card)) •
          A (fun _ => ∑ i ∈ S, v i) := by
  ...
```

Here `E` and `F` can be real normed spaces. For the immediate application, taking `E := EuclidD d` and `F := ℝ` reduces typeclass pressure.

Then uniqueness is short:

```lean
theorem ContinuousMultilinearMap.eq_zero_of_diag_eq_zero
    (A : E [×k]→L[ℝ] F)
    (hA : A.IsSymm)
    (hdiag : ∀ x, A (fun _ => x) = 0) :
    A = 0 := by
  apply ContinuousMultilinearMap.ext
  intro v
  have hpol := A.factorial_smul_eq_sum_diag hA v
  rw [show
    (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      ((-1 : ℝ) ^ (k - S.card)) •
        A (fun _ => ∑ i ∈ S, v i)) = 0 by
          apply Finset.sum_eq_zero
          intro S hS
          rw [hdiag]
          simp] at hpol
  have hk : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  exact (smul_eq_zero.mp hpol).resolve_left hk
```

Depending on the codomain and available lemmas, the last line may instead be discharged by applying `(k.factorial : ℝ)⁻¹ • ·` or by `simpa [hk]` after `eq_zero_of_smul_eq_zero`.

### Expansion of one diagonal term

Let:

```lean
let U : Finset (Fin k) := Finset.univ
```

For each `S : Finset (Fin k)`, use:

```lean
A.toMultilinearMap.map_sum_finset
```

with the same indexing finset in every argument:

```lean
fun _ : Fin k => S
```

and summand:

```lean
fun (_ : Fin k) (j : Fin k) => v j
```

Schematically:

```lean
have hexpand (S : Finset (Fin k)) :
    A (fun _ => ∑ j ∈ S, v j) =
      ∑ r ∈ Fintype.piFinset (fun _ : Fin k => S),
        A (fun i => v (r i)) := by
  simpa using
    A.toMultilinearMap.map_sum_finset
      (fun _ : Fin k => S)
      (fun (_ : Fin k) (j : Fin k) => v j)
```

The exact order of explicit arguments should be adjusted from `#check MultilinearMap.map_sum_finset`, but this is the intended instantiation.

Membership in the selector finset is expressed by:

```lean
Fintype.mem_piFinset
```

so that:

```lean
r ∈ Fintype.piFinset (fun _ : Fin k => S)
```

reduces to:

```lean
∀ i, r i ∈ S
```

Equivalently, if:

```lean
let R : Finset (Fin k) := Finset.univ.image r
```

then the condition is `R ⊆ S`.

### Swapping the two sums

After applying `hexpand`, normalize the dependent selector sum into a sum over all functions:

```lean
∑ r : Fin k → Fin k, ...
```

with an indicator for `∀ i, r i ∈ S`. Then use `Finset.sum_comm` to obtain:

```lean
∑ r : Fin k → Fin k,
  (∑ S ∈ U.powerset,
      if (∀ i, r i ∈ S)
      then (-1 : ℝ) ^ (k - S.card)
      else 0) •
    A (fun i => v (r i))
```

In practice it is useful to isolate this normalization as a local lemma rather than trying to make one long `rw` chain. The tools are:

```lean
Fintype.mem_piFinset
Finset.sum_comm
Finset.filter
Finset.sum_ite_irrel
```

The exact `sum_ite` lemma needed can vary with how the expression is normalized; a short `classical` proof using `Finset.sum_congr` is often more robust.

### The coefficient lemma

Prove separately:

```lean
lemma alternating_supersets
    (U R : Finset ι)
    (hRU : R ⊆ U) :
    ∑ S ∈ U.powerset.filter (fun S => R ⊆ S),
      ((-1 : ℝ) ^ (U.card - S.card))
      =
      if R = U then 1 else 0 := by
  ...
```

For the application, `U = Finset.univ`, so `U.card = k`.

I would not depend on a guessed one-shot theorem such as
`Finset.alternating_sum_powerset`: there is no standard, stable theorem with exactly the required supersets formulation. Likewise, converting first to `Int.alternating_sum_range_choose` introduces cardinal-grouping and cast work that is usually worse than a local finset induction.

A robust proof is:

1. Put `D := U \ R`.
2. Reindex supersets of `R` as `R ∪ T`, where `T ⊆ D`.
3. Use
   \[
   |U|-|R\cup T| = |D|-|T|.
   \]
4. Reindex by complement inside `D`, reducing to
   \[
   \sum_{T\subseteq D}(-1)^{|T|}.
   \]
5. Prove this is `1` for `D = ∅` and `0` otherwise by induction on `D`.

Relevant exact primitives include:

```lean
Finset.powerset_insert
Finset.sum_union
Finset.card_insert_of_notMem
Finset.card_sdiff
Finset.sdiff_eq_empty_iff_subset
Finset.disjoint_left
Finset.sum_bij
```

The final alternating-powerset sublemma can be kept very small:

```lean
lemma sum_powerset_neg_one (D : Finset ι) :
    ∑ T ∈ D.powerset, (-1 : ℝ) ^ T.card =
      if D = ∅ then 1 else 0 := by
  classical
  induction D using Finset.induction_on with
  | empty =>
      simp
  | @insert a D ha ih =>
      -- Split subsets according to whether they contain `a`.
      rw [Finset.powerset_insert ha]
      simp [ha, ih, pow_succ]
```

The last script may need a small `Finset.sum_union` step depending on the current statement of `Finset.powerset_insert`, but this is substantially less brittle than cardinal-grouping through binomial coefficients.

### From full range to bijectivity

For `r : Fin k → Fin k`, define:

```lean
let R := Finset.univ.image r
```

Then prove locally:

```lean
R = Finset.univ ↔ Function.Surjective r
```

by elementary membership reasoning. Since this is an endofunction of a finite type, surjectivity implies injectivity via:

```lean
Finite.injective_iff_surjective
```

Thus:

```lean
have hrbij : Function.Bijective r := by
  refine ⟨?_, hrsurj⟩
  exact (Finite.injective_iff_surjective).2 hrsurj
```

If the orientation of `Finite.injective_iff_surjective` differs in the installed version, swapping `.1` and `.2` is the only adjustment.

### Converting bijective functions to permutations

There is no need to search for a specialized equivalence. Define it using:

```lean
Equiv.ofBijective
Equiv.bijective
```

For example:

```lean
noncomputable def bijectiveEndEquivPerm :
    {r : Fin k → Fin k // Function.Bijective r} ≃
      Equiv.Perm (Fin k) where
  toFun r := Equiv.ofBijective r.1 r.2
  invFun σ := ⟨σ, σ.bijective⟩
  left_inv r := by
    ext i
    rfl
  right_inv σ := by
    ext i
    rfl
```

The cardinality computation is then:

```lean
have hcard :
    Fintype.card {r : Fin k → Fin k // Function.Bijective r}
      = k.factorial := by
  calc
    Fintype.card {r : Fin k → Fin k // Function.Bijective r}
        = Fintype.card (Equiv.Perm (Fin k)) :=
          Fintype.card_congr bijectiveEndEquivPerm
    _ = (Fintype.card (Fin k)).factorial := by
          simpa using Fintype.card_perm (Fin k)
    _ = k.factorial := by simp
```

The exact names requested are therefore:

- function to equivalence: `Equiv.ofBijective`;
- bijectivity of an equivalence: `Equiv.bijective`;
- transport of cardinality: `Fintype.card_congr`;
- cardinality of permutations: `Fintype.card_perm`;
- cardinality of `Fin k`: normally discharged by `simp`, using the `Fintype.card_fin` simp theorem.

### Finishing the polarization identity

After the coefficient calculation, only bijective `r` remain. For each such `r`, let:

```lean
let σ : Equiv.Perm (Fin k) := Equiv.ofBijective r hr
```

Then symmetry gives:

```lean
hA σ v :
  A (fun i => v (σ i)) = A v
```

which is definitionally or propositionally the required:

```lean
A (fun i => v (r i)) = A v
```

The remaining sum is one copy of `A v` for every permutation. Use `hcard` and `Finset.sum_const`/`simp` to turn it into:

```lean
(k.factorial : ℝ) • A v
```

---

## 3. Is there a slicker route?

Not presently in Mathlib in a way that is likely to shorten the proof.

### `mkPiRing`, divided powers, symmetric algebra

These abstractions can encode the mathematical fact, but using them would require proving that the associated homogeneous polynomial has the desired coefficient and then transporting that coefficient back to the continuous multilinear map. That is more infrastructure than the finite-subset proof and introduces coercion and scalar-denominator issues.

There is no ready-made Mathlib polarization theorem for `ContinuousMultilinearMap`.

### Ray derivatives

The identity

\[
\frac{d^k}{dt^k}L(tx)\bigg|_{t=0}
  = D^kL(0)(x,\ldots,x)
\]

only identifies the diagonal polynomial. It does not by itself recover mixed values.

To recover `A v₁ … vₖ` using

\[
(t_1,\ldots,t_k)\mapsto
L(t_1v_1+\cdots+t_kv_k),
\]

one must prove that its mixed derivative is `A(v₁,…,vₖ)`. In Lean this requires:

- a multivariable chain-rule calculation;
- identifying the derivative of the linear map
  `t ↦ ∑ i, t i • v i`;
- extracting a mixed coordinate derivative from `iteratedFDeriv`;
- permutation symmetry or coordinate-order independence.

That is essentially polarization plus more differentiability API. There does not appear to be a ready theorem giving this exact mixed-directional-derivative identity.

### Finite differences

One can present the proof conceptually as:

\[
\Delta_{v_1}\cdots\Delta_{v_k}
   \bigl[x\mapsto A(x,\ldots,x)\bigr](0)
   = k!\,A(v_1,\ldots,v_k).
\]

This is elegant mathematically, but expanding the finite differences produces exactly the same subset sum. Unless the project already has a finite-difference library, it does not reduce the Lean work.

Thus the subset-sum proof is the most direct and dependency-light route.

---

## 4. Precise minimal J3 API

I suggest these three declarations.

### Abstract symmetry predicate

```lean
namespace ContinuousMultilinearMap

def IsSymm
    (A : E [×k]→L[ℝ] F) : Prop :=
  ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E),
    A (fun i => v (σ i)) = A v
```

If Mathlib already has a suitably ergonomic symmetry predicate in the installed version, this can become an abbreviation or be replaced later.

### Core zero theorem

```lean
theorem eq_zero_of_diag_eq_zero
    (A : E [×k]→L[ℝ] F)
    (hA : A.IsSymm)
    (hdiag : ∀ x, A (fun _ => x) = 0) :
    A = 0
```

This is the fundamental J3 result.

### Equality form, best suited to J6

```lean
theorem eq_of_diag_eq
    (A B : E [×k]→L[ℝ] F)
    (hA : A.IsSymm)
    (hB : B.IsSymm)
    (hdiag : ∀ x, A (fun _ => x) = B (fun _ => x)) :
    A = B
```

This can either be proved by applying the zero theorem to `A - B`, after proving symmetry is preserved by subtraction, or directly by comparing the two polarization identities. The direct proof avoids setting up closure lemmas for `IsSymm`.

For the germbij application:

```lean
theorem iteratedFDeriv_eq_of_diag_eq
    {L₁ L₂ : EuclidD d → ℝ}
    (h₁symm :
      (iteratedFDeriv ℝ k L₁ 0).IsSymm)
    (h₂symm :
      (iteratedFDeriv ℝ k L₂ 0).IsSymm)
    (hdiag :
      ∀ x,
        iteratedFDeriv ℝ k L₁ 0 (fun _ => x) =
        iteratedFDeriv ℝ k L₂ 0 (fun _ => x)) :
    iteratedFDeriv ℝ k L₁ 0 =
      iteratedFDeriv ℝ k L₂ 0 :=
  ContinuousMultilinearMap.eq_of_diag_eq
    _ _ h₁symm h₂symm hdiag
```

Finally add a convenience wrapper whose regularity assumptions imply `h₁symm` and `h₂symm`, probably minimally at the base point:

```lean
theorem iteratedFDeriv_eq_of_diag_eq_of_contDiffAt_omega
    {L₁ L₂ : EuclidD d → ℝ}
    (h₁ : ContDiffAt ℝ ω L₁ 0)
    (h₂ : ContDiffAt ℝ ω L₂ 0)
    (hdiag : ∀ x, ...)
    : iteratedFDeriv ℝ k L₁ 0 =
        iteratedFDeriv ℝ k L₂ 0 := by
  apply ContinuousMultilinearMap.eq_of_diag_eq
  · intro σ v
    simpa using h₁.iteratedFDeriv_comp_perm ...
  · intro σ v
    simpa using h₂.iteratedFDeriv_comp_perm ...
  · exact hdiag
```

The final `simpa` arguments depend on the orientation and explicit arguments of the installed `ContDiffAt.iteratedFDeriv_comp_perm`; keeping that adaptation in this wrapper is exactly why the abstract J3 theorem is the better public foundation.