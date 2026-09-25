Your proposed trace formula is correct. The main qualification is geometric: **“relative interior” implies every active coordinate vanishes only if the limiting face is not contained in any active coordinate hyperplane.** Make that condition—or the lemma deriving it from your current assumptions—explicit.

## 1. Exact trace model: use measurable hypotheses

For the nonnegative theorem I would assume, only on `Ioo 0 ρ`:

- `Measurable w`, `Measurable a` (restricted measurability suffices);
- `0 ≤ w u ≤ W_*`;
- `0 < a_-` and `a_- ≤ a u`.

No continuity or upper bound on `a` is needed. State the corresponding signed theorem with `|w u| ≤ W_*` as a corollary. Your shifted-positive decomposition works; `w⁺ − w⁻` is another option.

The domination is exactly
\[
W_*e^{-\beta s-\eta h}
 \exp\!\left[-B\rho^{\sum\kappa}a_-e^{-s}\right],
\]
times the existing normalized fibre-volume bound.

**Open versus closed cut:** there is no trace-regularity issue. In transverse coordinates, changing `h > h₀` to `h ≥ h₀` changes a null hyperplane; after substitution, the endpoint `u = ρ` is null. Prove this using the transverse change of variables, rather than claiming that arbitrary measurable maps preserve null sets.

Your limit is
\[
C_{\rm geom}\int_0^\rho u^{q\eta-1}w(u)a(u)^{-\beta}\,du,
\qquad
C_{\rm geom}
=
A\Gamma(\beta)B^{-\beta}qD^{-q\eta}
\frac{\operatorname{vol}(F')}{|\det M|}.
\]

## 2. Chart observables: yes, Dirac for \(I=\varnothing\)

Yes: if every active coordinate tends to zero almost everywhere in the limiting fibre, observables `φ(x)` produce
\[
\phi(0)\,c,
\qquad
c=C_{\rm geom}\int_0^\rho
u^{q\eta-1}W_0(0,u)a_0(0,u)^{-\beta}\,du.
\]

Thus the chart-coordinate measure is `c • dirac 0`, and its pushforward is `c • dirac (rep 0)` when `rep` is continuous at zero. The non-Dirac warning concerns the **augmented observable space seeing \(u\)**; its projection to active chart coordinates is indeed Dirac.

With spectators, the measure is supported on `x_J = 0`, but for general units it is **not merely a constant times** the product power density. Its spectator density is
\[
\frac{A\Gamma(\beta)B^{-\beta}qD^{-q\eta}\operatorname{vol}(F')}
     {|\det M|}
\left(\prod_i y_i^{d_i-1}\right)
\int_0^\rho u^{q\eta-1}
 W_0(y,0,u)a_0(y,0,u)^{-\beta}\,du.
\]
Then push forward by `y ↦ rep (y,0)`. Constant units recover the product density already proved.

## 3. Trace replacement: pointwise sectional traces suffice

Your scaling argument is the right one, but apply it to the **whole amplitude including the exponential**, not only to `W`.

For fixed `(s,h)`, put `u = u(h)` and prove
\[
\begin{aligned}
L^{-k}\int_{\mathrm{fibreSet}_L(s,h)}
&W(x(z),u)\exp[-C\,a(x(z),u)e^{-s}]\,dz'\\
&\longrightarrow
\operatorname{vol}(F')W(0,u)
 \exp[-C\,a(0,u)e^{-s}],
\end{aligned}
\]
where \(C=B\rho^{\sum\kappa}\).

Sufficient analytic hypotheses are:

- joint measurability of `W` and `a`;
- a global bound `|W(x,u)| ≤ W_*` on the integration domain;
- a global lower bound `a_- ≤ a(x,u)`, with `a_- > 0`;
- for each `u ∈ (0,ρ)`,
  \[
  W(x,u)\to W_{\rm tr}(u),\qquad
  a(x,u)\to a_{\rm tr}(u)
  \quad\text{as }x\to0\text{ within }(0,\rho)^n;
  \]
- measurable trace functions, with the corresponding bounds.

No uniformity in `u` is necessary: fixed-`u` convergence gives the inner limit, and your outer DCT supplies uniform domination. Requiring these traces for every `u` is cleaner in Lean than the slightly more general almost-everywhere version.

### The precise geometric requirement

Write the leading scaled reconstructed coordinates as `α_j(w)`. What you need is
\[
\alpha_j(w)>0\quad\text{for every }j,\quad
\text{for a.e. }w\in F'.
\]

If `F'` is full-dimensional and each nonnegative affine `α_j` is not identically zero on it, the exceptional sets are null. But **relative boundary nullity alone does not prove this**: a face may lie entirely in `α_j = 0`.

No trace conditions are required on exceptional fibre-boundary points. The global amplitude bound and positive lower bound on `a` must still hold there. For `k = 0`, check positivity at the single limiting fibre point explicitly; a bad point is not null for zero-dimensional volume.

Also retain your existing fixed-compact-support bound for the scaled fibre indicators. That, rather than boundedness of `W` alone, gives the inner DCT majorant.

## 4. The single theorem and implementation order

I would expose a general theorem schematically as follows:

```lean
-- Existing active-truth geometric/certificate hypotheses,
-- plus a.e. strict positivity of all leading active coordinates.

-- On x ∈ (0,ρ)^n and u ∈ (0,ρ):
--   W, a jointly measurable
--   |W x u| ≤ Wstar
--   0 < amin ≤ a x u
-- For every u ∈ (0,ρ), along x → 0 within the positive box:
--   W x u → Wtr u
--   a x u → atr u
-- Wtr, atr measurable, with the same bounds.

Tendsto
  (fun t ↦ normalization t * modelKernel ... W a t)
  atTop
  (𝓝 (Cgeom *
    ∫ u in Set.Ioo 0 ρ,
      u ^ (q * η - 1) * Wtr u * atr u ^ (-β)))
```

For the `lintegral` implementation, prove its nonnegative version first and derive the signed version by linearity.

**Recommended order:**

1. **Exact measurable trace model.** Land your proposed theorem as the low-risk checkpoint; isolate the `h ↔ u` integral identity.
2. **Weighted fibre convergence lemma.** Package the scaled-fibre DCT with a general bounded amplitude having an active-coordinate trace.
3. **General trace-replacement theorem** above. The exact model becomes an immediate specialization.
4. **No-spectator chart wrapper now.** Apply the theorem to  
   `Wφ(x,u) = φ(rep x) * W₀(x,u)`. This validates the certificate interface before another spectator layer.
5. **Spectator extension**, then its chart wrapper. Reuse the outer-DCT machinery with uniform amplitude bounds and uniform positive lower bounds.

So: do not duplicate the whole pipeline for (i) and (ii), but do retain (i) as a named theorem and test case.

## 5. Positivity and certificate outputs

Assuming `A ≥ 0`, all geometric and analytic factors are nonnegative, hence `0 ≤ c`. If `A` is genuinely signed, positivity does **not** follow; keep the analytic theorem valid for arbitrary `A`, and require `0 ≤ A` in the positive-measure wrapper.

I would provide three companion lemmas:

- **trace integral integrable**, using
  \[
  |u^{q\eta-1}W_{\rm tr}(u)a_{\rm tr}(u)^{-\beta}|
  \le W_*a_-^{-\beta}u^{q\eta-1};
  \]
- **coefficient nonnegative** under `A ≥ 0` and `Wtr ≥ 0`;
- optionally **coefficient strictly positive**, requiring `A > 0`, positive face volume, and `Wtr > 0` almost everywhere.

The last lemma matters only if the interface needs a nonzero leading measure: positive units do not compensate for a zero-volume limiting face.

For `TermMeasureCertificate`, the analytic payload is the correctly normalized observable limit and a finite positive measure. Comparison/minimality of `lam₀, k₀` across terms remains bookkeeping, not part of this local analytic theorem.