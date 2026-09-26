## Recommendation: avoid general polyhedral continuity altogether

There is a substantially cheaper route than (a)–(e), using the **Pythagoras theorem you already have**:

> The entropy minimiser has maximal support in its moment fibre. On a finite simplex, this gives exactly the local recovery construction needed for continuity.

This proves continuity of `q*` **before** continuity of the value function. No Hoffman estimate, local conicity, triangulation, or parameterised face induction is needed.

I would make this the next module.

## 1. Continuity: the lemma chain

Work initially with probability vectors
\[
\Delta=\{p:X\to\mathbb R:\ p_x\ge0,\ \sum_xp_x=1\},
\qquad
A p=\sum_xp_xS(x).
\]
Normalize the positive weights to a probability vector \(w\). Unnormalized weights only add a constant to the objective.

Use the real-valued continuous entropy
\[
D_w(p)=\sum_x p_x\log p_x-\sum_xp_x\log w_x,
\]
with \(0\log0=0\). Its continuity on \(\Delta\) follows from continuity of `Real.xlogx`. Connect this objective once to measure-theoretic `klDiv`.

### Lemma 1: all fibres over \(C\) are nonempty and have finite rate

Prove
\[
A(\Delta)=\operatorname{conv}(S(X)).
\]

This is the finite convex-combination characterization of convex hull; Carathéodory is unnecessary. Every probability vector has finite KL against positive \(w\). Thus the entropy bound gives finite rate throughout \(C\), and your existing existence/uniqueness theorem supplies `qStar`.

### Lemma 2: maximal support, directly from Pythagoras

For \(m\in C\), write \(p=q^*(m)\). If \(r\in\Delta\) has \(Ar=m\), then
\[
D_w(r)=\mathrm{KL}(r\Vert p)+\mathcal I(m).
\]
The left side is finite. Therefore \(\mathrm{KL}(r\Vert p)<\infty\), hence \(r\ll p\). On a finite alphabet:
\[
\boxed{Ar=m,\quad r_x>0\quad\Longrightarrow\quad q^*(m)_x>0.}
\]

This avoids the usual \(t\log t\) directional-derivative argument entirely.

Lean-level API sketches below use proposed names, not claimed existing declarations:

```lean
def ProbVec (X : Type*) [Fintype X] :=
  ↥(stdSimplex ℝ X)

def moment (p : ProbVec X) : E :=
  ∑ x, (p : X → ℝ) x • S x

theorem support_le_qStar
    (m : C) (r : ProbVec X)
    (hr : moment S r = (m : E)) :
    ∀ x, 0 < (r : X → ℝ) x →
      0 < (qStar m : X → ℝ) x
```

### Lemma 3: finite-simplex additive recovery

Suppose \(a_n\to r\) in \(\Delta\), and \(p\in\Delta\) satisfies
\[
\operatorname{supp}(r)\subseteq\operatorname{supp}(p).
\]
Then, eventually,
\[
b_n=p+a_n-r\in\Delta,\qquad b_n\to p.
\]

The sum is exactly one. Coordinatewise:

* if \(p_x>0\), then \(b_{n,x}\to p_x>0\);
* if \(p_x=0\), support inclusion gives \(r_x=0\), so \(b_{n,x}=a_{n,x}\ge0\).

Finiteness of \(X\) makes these coordinatewise eventual statements simultaneous. Moreover,
\[
A b_n=A p+A a_n-A r.
\]

```lean
theorem eventually_mem_stdSimplex_add_sub
    (p r : ProbVec X) (a : ℕ → ProbVec X)
    (ha : Tendsto a atTop (𝓝 r))
    (hsupp : ∀ x, 0 < (r : X → ℝ) x →
                        0 < (p : X → ℝ) x) :
    ∀ᶠ n in atTop,
      ((p : X → ℝ) + (a n : X → ℝ) - (r : X → ℝ))
        ∈ stdSimplex ℝ X
```

This is a qualitative lifting lemma **at a support-saturated point**, not lower hemicontinuity at every point of every fibre. That weaker statement is all you need.

### Lemma 4: limits of minimisers are minimisers

Suppose \(m_n\to m\), and a subsequence of \(q^*(m_n)\) converges to \(r\). Continuity of the moment map gives \(Ar=m\).

Set \(p=q^*(m)\). Lemma 2 gives \(\operatorname{supp}(r)\subseteq\operatorname{supp}(p)\). Consequently
\[
b_n=p+q^*(m_n)-r
\]
is eventually feasible for \(m_n\), and converges to \(p\). Optimality gives
\[
D_w(q^*(m_n))\le D_w(b_n).
\]
Passing to the limit:
\[
D_w(r)\le D_w(p).
\]
Since \(r\) is feasible at \(m\), uniqueness implies \(r=p\).

Compactness of \(\Delta\) now proves continuity of `qStar`: every convergent subsequence limit is the required one.

```lean
theorem qStar_limit_eq
    (m : C) (ms : ℕ → C) (r : ProbVec X)
    (hm : Tendsto ms atTop (𝓝 m))
    (hr : Tendsto (fun n => qStar (ms n)) atTop (𝓝 r)) :
    r = qStar m

theorem continuous_qStar :
    Continuous (qStar : C → ProbVec X)

theorem continuous_value :
    Continuous (fun m : C => entropy w (qStar m))
```

The value-function theorem is now simply composition.

**The single lemma I would budget most carefully is the compactness-to-continuity wrapper around `qStar_limit_eq`.** Its mathematics is elementary, but subsequence/filter bookkeeping is likely the largest Lean cost. The new mathematical core is `eventually_mem_stdSimplex_add_sub`, which is short and independent of convex geometry.

You can package the wrapper as a reusable continuous-argmin theorem for a finite simplex, continuous objective, linear constraints, unique minimisers, and the support-saturation hypothesis.

### Why not the other routes?

* (a), (b), and (e) prove substantially more geometry than necessary.
* (c) still needs a transverse boundary-matching argument; continuity on individual faces alone does not supply it.
* (d) does not give the desired upper bound. For the convention \(Q_\theta\propto w e^{-\langle\theta,S\rangle}\), the correct identity is
  \[
  D_w(r)=\mathrm{KL}(r\Vert Q_s)+\mathcal I(M_s)
       -\langle\theta_s,Ar-M_s\rangle.
  \]
  The extra term vanishes only when \(Ar=M_s\); moreover, KL nonnegativity points toward a lower bound.

## 2. Support equals the minimal face

In fact, support identification need not wait for continuity.

Define the accessible indices at \(m\):
\[
J_m=\{x:\exists r\in\Delta,\ Ar=m,\ r_x>0\}.
\]
Maximal support immediately gives
\[
\operatorname{supp}q^*(m)=J_m.
\]

The remaining finite-polytope lemma is
\[
\boxed{x\in J_m\iff S(x)\in F_m.}
\]

There are two routes.

### Existing face API / exposed-face induction

If your induction already identifies the minimiser with a full-support tilt of the prior restricted to the **minimal face**, positivity is immediate. Restriction to one exposed face is not enough unless that face is minimal; recurse until the mean is in the relative interior of the restricted polytope.

All polytope faces are exposed, but I would avoid making continuity depend on formalizing that theorem.

### Elementary alternative: construct the minimal face from the support

Let \(p=q^*(m)\), \(J=\operatorname{supp}p\), and
\[
D=\operatorname{conv}\{S(x):x\in J\}.
\]

1. \(m\in D\).
2. Every face containing \(m\) contains each \(S(x)\) with \(p_x>0\), hence contains \(D\).
3. \(D\) is itself a face.

For step 3, take \(y\in D\). Choose a probability vector \(b\), supported in \(J\), with \(Ab=y\). Since \(p\) is strictly positive on \(J\), choose \(0<\varepsilon<1\) with \(\varepsilon b\le p\). Thus
\[
m=\varepsilon y+(1-\varepsilon)z,\qquad z\in D.
\]
If \(y=t u+(1-t)v\), with \(u,v\in C\) and \(0<t<1\), lift \(u,v\) to probability vectors. This expresses \(m\) using each lift with positive coefficient. Support saturation forces both lifts to be supported in \(J\), so \(u,v\in D\).

Hence \(D=F_m\). Finally, if \(S(x)\in D\), the same small-\(\varepsilon\) construction, now using \(\delta_x\), produces a feasible vector positive at \(x\).

```lean
theorem qStar_pos_iff_mem_minimalFace
    (m : C) (x : X) :
    0 < (qStar m : X → ℝ) x ↔
      S x ∈ minimalFace C (m : E)
```

This handles repeated feature values automatically. It also gives the usual topological support statement for the associated measure when `X` has its discrete topology.

## 3. Closure, homeomorphism, retraction, deformation

### Use probability vectors as the primary type

For these topological statements, use `ProbVec X`, not measures. Finite sums, convex combinations, compactness, and continuity are all direct. Add a separate conversion
\[
p\longmapsto\sum_x p_x\,\delta_x
\]
to connect to `responseProjection`.

On a finite alphabet, vector convergence is equivalent to TV convergence, with the usual convention
\[
d_{\mathrm{TV}}(p,q)=\tfrac12\sum_x|p_x-q_x|.
\]

Let:

```lean
def momentToPolytope : ProbVec X → C := ...

def completed : Set (ProbVec X) :=
  Set.range qStar

def retract (p : ProbVec X) : ProbVec X :=
  qStar (momentToPolytope S p)
```

Basic statements:

```lean
theorem moment_qStar (m : C) :
    momentToPolytope S (qStar m) = m

theorem continuous_retract :
    Continuous (retract S w)

theorem moment_retract (p : ProbVec X) :
    momentToPolytope S (retract S w p) =
      momentToPolytope S p

theorem retract_qStar (m : C) :
    retract S w (qStar m) = qStar m

theorem retract_idempotent (p : ProbVec X) :
    retract S w (retract S w p) = retract S w p

theorem retract_eq_self_iff (p : ProbVec X) :
    retract S w p = p ↔ p ∈ completed S w
```

Restricting the codomain gives a genuine retraction onto the subtype:

```lean
def retractToCompleted :
    ProbVec X → ↥(completed S w) := ...
```

The homeomorphism needs no compact-Hausdorff argument: both inverse maps are already continuous.

```lean
def completedHomeomorph :
    C ≃ₜ ↥(completed S w) := ...
```

Its forward map is `qStar`; its inverse is the restricted moment map.

For closure, the completed set is compact, hence closed. For any \(m\in C\), choose an interior anchor \(m_0\); the means
\[
m_s=(1-s)m_0+s m,\qquad s<1,
\]
are interior and converge to \(m\). Continuity and interior identification give
\[
\overline{\{\text{interior family laws}\}}=\operatorname{range}(q^*).
\]
Use **relative interior** if the features do not affinely span the ambient space. Your existing endpoint convergence also proves this density direction.

### Strong deformation retraction

Let `I := Set.Icc (0 : ℝ) 1`. Define, with the simplex-membership proof built in:

```lean
def deformation (t : I) (p : ProbVec X) : ProbVec X :=
  -- underlying vector:
  -- (1 - (t : ℝ)) • p + (t : ℝ) • retract S w p
  ...
```

The clean theorem bundle is:

```lean
theorem continuous_deformation :
    Continuous (fun z : I × ProbVec X =>
      deformation S w z.1 z.2)

theorem deformation_zero (p : ProbVec X) :
    deformation S w 0 p = p

theorem deformation_one (p : ProbVec X) :
    deformation S w 1 p = retract S w p

theorem deformation_fixed
    (t : I) (p : ProbVec X) (hp : p ∈ completed S w) :
    deformation S w t p = p

theorem moment_deformation (t : I) (p : ProbVec X) :
    momentToPolytope S (deformation S w t p) =
      momentToPolytope S p

theorem retract_deformation (t : I) (p : ProbVec X) :
    retract S w (deformation S w t p) = retract S w p
```

These explicit statements can subsequently be bundled into whichever homotopy API is most convenient.

## 4. Priority and smallest landable modules

**Do face completion next.** The explicit analytic radius remains valuable for certified truncations and uniform numerical estimates, but it does not unlock as much structure as the completed-family topology.

Suggested increments:

1. **`FiniteEntropySupport`**  
   Probability-vector/measure bridge, continuous finite entropy, finite rate on \(C\), and maximal support from Pythagoras.

2. **`FiniteCompletionContinuity`**  
   Additive recovery lemma, limit identification, continuity of `qStar`, then continuity of the value.

3. **`FiniteMinimalFace`**  
   Accessible-support characterization and support equals minimal face.

4. **`FiniteCompletionRetraction`**  
   Closure, homeomorphism, retraction, and fibrewise strong deformation retraction.

The smallest useful first landing is **maximal support**, not value-function continuity. It is the missing structural observation that makes the continuity proof short.