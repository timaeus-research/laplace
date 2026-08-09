# Tide: germbij tensor J6 (single-degree recovery)

**Direction (user):** standing auto-mode commission; the consult's
composition stage.
**Seabed:** laplace, branch tide/germbij-tensor-normrate at 57bef28
(stacked on unmerged J5e, PR #80).
**Started:** 2026-08-09T14:10 local

## Candidates

Consult J6, with symmetry per the J3 abstract ruling:

1. Certificates for the diagonal term: `taylorHomogeneousTerm` is
   continuous (CMM continuity composed with the diagonal) and of
   polynomial growth (`le_opNorm` with ∏‖x‖ = ‖x‖^k).
2. **`iteratedFDeriv_recovery_of_moment_rates`**: matched jets below
   k, abstract IsSymm of both k-th tensors, and the o(q^{k−2})
   moment-difference data for every continuous polynomial-growth
   homogeneous-degree-k test P, force
   iteratedFDeriv ℝ k L₁ 0 = iteratedFDeriv ℝ k L₂ 0.
   Proof (the consult's seven steps): instantiate the data at
   P := Q (the diagonal difference — its certificates are step 1 +
   J4 homogeneity); IsLittleO → the divided Tendsto → 0; J5e gives
   → −Cov(Q,Q); uniqueness of limits kills the covariance; J2
   rigidity kills Q; cancel (k!)⁻¹ to equal diagonals; J3
   polarization upgrades to tensor equality.

## Numerical check

Pure composition of verified components; no new closed form.

## Vote

- Claude: J6 as staged. - GPT-5.6 Sol: same (archived). Agreed.
