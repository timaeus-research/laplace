# Tide: germbij-gamma-jn2b (stage 2b of the gamma-rung programme)

**Direction (user):** gamma-rung programme stage 2, second half: the
quadratised six-term integral decomposition and the second-order J_n
asymptotic headline.

**Seabed:** laplace, chained on tide/germbij-gamma-jn2 (stage 2a, merged
as b7bf599 mid-tide; branch rebased onto main at close-out). Consumes
perturbation_remainder3_integral_bound (2a), integrable_J_n
(de-privatised in this tide, one-word change justified by second use),
and the linearised layer's architecture.
**Worktree/branch:** laplace-tide-germbij-gamma-jn2b /
tide/germbij-gamma-jn2b
**Started:** 2026-08-09T20:10Z

## Deliberation (programme-inherited)

Stage specified in the scoping consult. Execution choice: the pointwise
six-term identity is proven with the sqrt(t)-ATOM SUBSTITUTION — after
`set st := Real.sqrt t`, the goal's remaining bare t's are rewritten by
t = st * st, making the s_t^2 expansion rational in st so field_simp +
ring close it with no (sqrt t)^2 = t relation needed mid-ring. This is
the trick anticipated at scoping for the square's cross terms.

## Result

- Branch tide/germbij-gamma-jn2b, Laplace/OneD/JnSecondOrder.lean:
  quadratised_integrand_eq (private), quadratised_integral_decomposition
  (six moment terms), J_n_asymptotic_order2 (the stage headline:
  J_n = m_n - A/sqrt(t) m_{n+3} - B/t m_{n+4} + A^2/(2t) m_{n+6}
  + O(1/(t sqrt t)), with the AB and B^2 cross-terms absorbed into the
  error constant explicitly). integrable_J_n de-privatised in
  IntegralRemainder.lean.
- Four build iterations: the Pi.sub gotcha inside an Integrable.congr
  (simp only [Pi.sub_apply] before ring — the documented family's
  fourth member); two dead tactics after gcongr closed side goals.
- Surprise: the sqrt(t)-atom substitution worked exactly as designed on
  the first attempt; the six-fold nested integral_add with type-ascribed
  cumulative witnesses (the CLAUDE.md Pi.add discipline) also compiled
  first try.

## Numerical check

Run before the log (scipy, (lam, alpha, gamma) = (1.3, 0.4, 0.9), n = 2):
|J_2 - main_order2| * t^{3/2} = 0.0261 (t=10), 0.0059 (t=100),
0.0018 (t=1000) — bounded (in fact decaying: the next order is
t^{-3/2} exactly from the AB m_9 odd-moment vanishing at n even... the
observed decay ~t^{-1/2} relative suggests the true next term here is
O(t^-2)), confirming the O(1/(t sqrt t)) claim with room.
