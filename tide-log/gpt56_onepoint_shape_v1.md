## A. Faithfulness of the function-level \(C(t)\) model

Yes—provided it is presented as the **flat-equivalence consequence** of equality of normalized asymptotic families, rather than as a literal definition of equality of formal asymptotic series.

Define, following the existing decay vocabulary,
\[
\operatorname{SuperPoly}(f)
\quad:\!\iff\quad
\forall N:\mathbb N,\;
f(t)=o_{t\to\infty}(t^{-N}).
\]

Then the useful hypothesis is
\[
\exists C:\mathbb R\to\mathbb R,\quad
\forall \phi\in\mathcal A,\quad
\operatorname{SuperPoly}\bigl(I_{2,\phi}-C I_{1,\phi}\bigr),
\]
where
\[
I_{i,\phi}(t)=\int \phi\,e^{-tL_i}.
\]

This retains exactly the consequence needed by Proposition 7.6.

### Qualifications

1. **One common \(C\) is essential.**  
   The quantifiers must be
   ```lean
   ∃ C, ∀ φ, ...
   ```
   and not `∀ φ, ∃ C`. The latter has almost no normalized-family content.

2. **It is not automatically equivalent to formal-series proportionality.**  
   Formal proportionality implies this function-level statement only after choosing a function realizing the formal scalar series, or after proving it directly from normalized ratio data. Conversely, the function-level statement forgets all coefficient-level information. That loss is harmless for this proof, since the final contradiction only uses beyond-all-orders equality.

3. **No regularity of \(C\) is needed.**  
   \(C\) is never integrated or differentiated. It only appears in pointwise products and asymptotic relations, so neither measurability nor continuity should be assumed.

4. **The anchor lower bound handles division safely.**  
   From
   \[
   I_{2,\phi_0}=I_{1,\phi_0}=:A
   \]
   and
   \[
   \operatorname{SuperPoly}(I_{2,\phi_0}-C I_{1,\phi_0}),
   \]
   one obtains
   \[
   \operatorname{SuperPoly}((1-C)A).
   \]
   If eventually
   \[
   \kappa t^{-a}\le A(t),\qquad \kappa>0,
   \]
   then \(A\) is eventually positive and division loses only a polynomial factor. Taking the superpolynomial estimate at order \(N+a\) gives the estimate for \(C-1\) at order \(N\).

There is therefore no hidden need to control \(C\) where the anchor moment vanishes: the lower bound ensures that it does not vanish eventually.

A useful strengthening is that exact anchor equality is more than necessary. It suffices to know
\[
\operatorname{SuperPoly}(I_{2,\phi_0}-I_{1,\phi_0}),
\]
because subtracting the two anchor relations still gives
\[
\operatorname{SuperPoly}((C-1)I_{1,\phi_0}).
\]
Local equality naturally supplies exact equality, however.

---

## B. Cheapest decomposition and hypothesis shapes

The cleanest decomposition is measure-theory-free at the core.

### 1. Polynomial anchor cancellation

First prove a pure asymptotic lemma of the form:

```lean
theorem superpoly_of_mul_anchor
    (hflat : SuperPoly (fun t => (C t - 1) * A t))
    (hκ : 0 < κ)
    (hlow : ∀ᶠ t in atTop, κ * invPow t n ≤ A t) :
    SuperPoly (fun t => C t - 1)
```

Here `invPow t n` denotes whichever `t⁻¹ ^ n`, `t ^ (-n : ℤ)`, or existing Mathlib convention is already used in `Laplace.Decay`.

It is worth normalizing the lower bound to an **integer polynomial order**:
\[
\kappa t^{-n}\le A(t),\qquad n\in\mathbb N.
\]
If the sector machinery produces a real exponent \(a\), choose \(n\ge a\); eventually for \(t\ge1\),
\[
t^{-n}\le t^{-a}.
\]
That keeps the asymptotic algebra aligned with the existing `∀ N : ℕ` definition and avoids unnecessary `Real.rpow` arithmetic.

### 2. Remove the scalar from another observable

Then prove:

```lean
theorem remove_superpoly_scalar
    (hC : SuperPoly (fun t => C t - 1))
    (hJ : IsBigO atTop J (fun _ => 1))
    (hprop : SuperPoly (fun t => B t - C t * J t)) :
    SuperPoly (fun t => B t - J t)
```

The identity is
\[
B-J=(B-CJ)+(C-1)J.
\]
Superpolynomial functions are closed under addition and under multiplication by an eventually bounded function.

A more general version can allow
\[
J(t)=O(t^b),
\]
since a polynomial factor merely shifts the requested decay order. But the bounded version is cheaper and sufficient for Laplace moments under the stated hypotheses.

### 3. Package the family-level corollary

After those two lemmas, a convenient corollary is:

```lean
theorem anchored_proportionality_implies_equal
    (hprop : ∀ φ ∈ 𝒜,
      SuperPoly (fun t => I₂ φ t - C t * I₁ φ t))
    (hanchor : ∀ᶠ t in atTop, I₂ φ₀ t = I₁ φ₀ t)
    (hlow : ∀ᶠ t in atTop, κ * invPow t n ≤ I₁ φ₀ t)
    (hκ : 0 < κ)
    (hbounded : ∀ φ ∈ 𝒜, IsBigO atTop (I₁ φ) (fun _ => 1)) :
    ∀ φ ∈ 𝒜,
      SuperPoly (fun t => I₂ φ t - I₁ φ t)
```

It may be cheaper in Lean to quantify over one target observable at a time rather than carrying a class:

```lean
theorem anchored_proportionality_remove_scalar
    (hprop₀ : SuperPoly (fun t => I₂₀ t - C t * I₁₀ t))
    (hanchor : ∀ᶠ t in atTop, I₂₀ t = I₁₀ t)
    (hlow : ...)
    (hprop : SuperPoly (fun t => I₂ t - C t * I₁ t))
    (hbounded : IsBigO atTop I₁ (fun _ => 1)) :
    SuperPoly (fun t => I₂ t - I₁ t)
```

This avoids committing the generic asymptotic library to a particular observable-class representation.

### Moment upper bound

For \(L\ge0\), \(t\ge0\), and integrable \(\phi\),
\[
\left|\int \phi(x)e^{-tL(x)}\,dx\right|
\le \int |\phi(x)|e^{-tL(x)}\,dx
\le \int |\phi(x)|\,dx.
\]

Thus the best abstract hypothesis is simply

```lean
IsBigO atTop (I₁ φ) (fun _ => 1)
```

or an eventual bound `|I₁ φ t| ≤ M`.

A separate analytic lemma can derive it from:

- `0 ≤ L₁` almost everywhere on the relevant region,
- eventual `0 ≤ t`,
- integrability of `φ`.

Using `∫ |φ|` is generally cheaper than explicitly introducing `volume (support φ) * sup ‖φ‖`, although the latter is also valid for continuous compactly supported observables.

### Local equality and exact anchor equality

Keep the main anchoring interface as local equality:

```lean
hlocal : Set.EqOn L₁ L₂ V
htsupport : tsupport φ₀ ⊆ V
```

From these, derive the moment equality rather than assuming it separately. Outside `V`, `φ₀` vanishes; inside `V`, the exponentials agree.

The ratio-recovery and additive-constant argument can remain a separate small lemma:

```lean
L₂ x = L₁ x + c on V
p ∈ V
L₁ p = 0
L₂ p = 0
⊢ c = 0
```

This is conceptually useful but should not be entangled with the asymptotic cancellation lemma.

---

## C. Minimal first tide

The best first tide is **lemma (A), as pure asymptotic algebra**, ideally split into two reusable pieces:

1. polynomially nonvanishing anchor:
   \[
   \operatorname{SuperPoly}((C-1)A)
   \land A\gtrsim t^{-n}
   \Longrightarrow
   \operatorname{SuperPoly}(C-1);
   \]

2. gauge removal:
   \[
   \operatorname{SuperPoly}(C-1)
   \land J=O(1)
   \land \operatorname{SuperPoly}(B-CJ)
   \Longrightarrow
   \operatorname{SuperPoly}(B-J).
   \]

Then add a short packaged corollary combining them.

This tide has several advantages:

- no measure theory;
- no analyticity;
- no support bookkeeping;
- no dependence on the precise API of the pencil/sector theorem;
- directly reusable for other normalized asymptotic arguments;
- it isolates the only genuinely new algebra in Proposition 7.6.

The next tide should add:

1. the constant moment bound for compactly supported observables;
2. derivation of exact anchor moment equality from local equality and support;
3. a thin final wrapper invoking the existing singular-identifiability contradiction theorem.

The final wrapper should be logically very small: if failure of equality near \(W_0\) lets the existing pencil/sector theorem produce an observable \(\phi\) whose moment difference is **not** superpolynomial, the family-level cancellation result supplies that it **is** superpolynomial, a contradiction.

So the recommended order is:

1. **pure `SuperPoly` anchor cancellation;**
2. **Laplace-moment boundedness and local anchor instantiation;**
3. **composition with the existing turnkey identifiability theorem.**

That is cheaper and less brittle than formalizing the full one-point-anchoring theorem in one tide.