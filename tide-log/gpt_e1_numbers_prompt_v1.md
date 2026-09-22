# Tide `e1-numbers` (laplace seabed): candidates for GPT-6 Astra

## Context

E1 (step size on quadratic potentials, `d = 10`, `t = 100`) reports: "Against the plain Laplace value the stiffest direction is inflated
by exactly `1/(1 − lr·pmax/2)`: a factor `2.0` at `lr·pmax = 1`, `4.0` at `1.5`, `20` at `1.9`" and "At `κ = 1`, where all directions
are equally stiff, `t⟨K⟩ = 10, 20, 100` at `lr·pmax = 1, 1.5, 1.9` against the true `5`". E5 (Rosenbrock `d = 2`, `κ ≈ 2500`):
"SGLD at `lr·pmax = 0.5` gives `1.17 = (1 + 4/3)/2`, the ULA law applied to the stiff direction only". The seabed has the ULA law
`ulaCov_conj_apply` (eigenbasis diagonal `1/(pᵢ(1 − hpᵢ/2))`), `ula_llc` (`t/2 tr(H Σ_ULA) = ½ ∑ᵢ 1/(1 − hpᵢ/2)`),
`sum_one_div_one_sub_bounds`, and E1's third finding already (`iat_flat_e1 : τ_flat = 2/(h pmin) − 1 = 199 999`).

## Candidates (all elementary; `norm_num`)

**A.** `ulaCov_conj_diag_ratio`: the ULA eigenbasis variance over the Laplace value is `1/(1 − hpᵢ/2)`, and
`ula_inflation_values : 1/(1 − 1/2) = 2 ∧ 1/(1 − 1.5/2) = 4 ∧ 1/(1 − 1.9/2) = 20`.

**B.** `ula_llc_isotropic`: if all eigenvalues of `tH` equal `p`, `t/2 tr(H Σ_ULA) = d/(2(1 − hp/2))`;
`ula_llc_isotropic_e1 : 10/(2(1 − 1/2)) = 10 ∧ 10/(2(1 − 1.5/2)) = 20 ∧ 10/(2(1 − 1.9/2)) = 100`.

**C.** `ula_llc_rosenbrock_bound`: for `d = 2` with eigenvalues `p` and `p/κ`, `hp = 1/2` and `κ ≥ 2500`,
`|t/2 tr(H Σ_ULA) − 7/6| ≤ 10⁻⁴` (the flat direction contributes `½/(1 − 1/(4κ)) ∈ [½, ½·10000/9999]`), so "1.17" is `7/6` to the
displayed precision, and it is `(1 + 4/3)/2` with the stiff factor `4/3 = 1/(1 − 0.25)` and the flat factor `≈ 1`.

## Questions

1. Are the readings of the three sentences right (in particular E5's "ULA law applied to the stiff direction only" as the two-term
   sum with the flat factor `1/(1 − 1/(4κ)) ≈ 1`)? The note's E5 statement is about SGLD on the *non-Gaussian* Rosenbrock target; the
   seabed's `ula_llc` is for Gaussian targets, so C certifies the *arithmetic of the explanation*, not the sampler result — is that
   the right caveat?
2. Is a tide of exact numerical corollaries worth landing (they tag three quoted numbers in E1/E5 directly), or should they be folded
   into a larger tide? Anything else in E1 that is a clean corollary (e.g. `κ = 1000`'s `5.7, 6.9, 15` needs the log-uniform
   spectrum `100^{i/9}`-type powers, which we propose to skip)?
3. Vote (A+B+C)?
