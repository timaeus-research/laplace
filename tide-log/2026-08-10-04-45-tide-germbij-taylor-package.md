# Tide: germbij-taylor-package (smooth-germ programme, stage C2)

**Direction (user):** the analytic estimates package (auto mode,
standing delegation): Peano remainder in epsilon form, the stabilized
Taylor polynomial with the coefficient-wise d construction and global
envelope (a₂/2)x² ≤ P, Gaussian-scale integral bounds, partition
lower / moment upper bounds, and superpolynomial tails outside the
moving radius q^{4/5} — everything C3's comparison theorem consumes.

**Seabed:** laplace, main at 89633f6 (C1 merged).
**Worktree/branch:** laplace-tide-germbij-taylor-package /
tide/germbij-taylor-package
**Started:** 2026-08-10T04:45Z

## Programme scoping

Consult saved verbatim: `tide-log/gpt56_smooth_germ_scoping_v1.md`
(with the germbij note attached as context). Key rulings: the fixed
moving split |x| ≤ q^{4/5} = t^{-2/5} suffices at every finite order
PROVIDED the proof integrates the Taylor power |x|^D inside the
Gaussian rather than sup-ing t|L−T| over the inner region (the sup
loses powers as R grows); Taylor degree D = R+2 suffices (R+4 is
overkill); the stabilizer needs M > D = R+2 (not merely M > R — it
first appears at rung M−2), least even integer above D; and d has an
elementary coefficient-wise formula d ≥ Σ|a_j|ρ^{j−M} with
ρ = min(1, a₂/(2(B+1))), B = Σ|a_j|, giving the global envelope
P(x) ≥ (a₂/2)x² by a case split at |x| = ρ — no suprema needed. C3
(the normalized comparison) is named the single hardest stage; C2's
job is to package every estimate it needs.

## Vote

- Claude: C2 as one tide with the five sub-lemmas (C2.1-C2.5).
- GPT-5.6 Sol: same staging (its own plan).

Agreed.

## Numerical check

Executed before formalisation (values quoted from output). (1)
Stabilizer construction at L = 0.9x² − 0.7x³ + 0.2x⁴ (D = 4, M = 6):
B = 0.900, ρ = 0.2368, d = 56.255; min over [−6,6] of P − (a₂/2)x²
is 0.000000 (attained at 0), confirming the global envelope. (2) A
raw decay check of q^{-N}·tail is numerically INFEASIBLE: the
superpolynomial regime needs q^{-2/5} ≫ N·ln(1/q), i.e. q < 2.6e−6
for N = 6 — so the check was replaced by its inequality-level driver:
t·P(x) ≥ (a₂/2)q^{-2/5} on |x| ≥ q^{4/5} verified pointwise on a grid
at q ∈ {0.1, 0.03, 0.005}. Honest note: the first tail check (raw
q^{-6}·tail at q = 0.1, 0.03) produced GROWING values (123 → 1541),
which is the pre-asymptotic regime, not a counterexample; recorded
here so the C3 tide knows the numerics cannot certify the tail rate
directly.

## Scope adjustment

C2.4's partition LOWER bound (C₀·q ≤ Z_K) requires an upper envelope
on K near 0 — an admissibility hypothesis that belongs with C3's
SmoothAdmissible setup, where the hypothesis package for the smooth
loss is fixed. Re-scoped to the C3 tide. C2.4's upper half (moment
upper bounds) is subsumed by C2.3 + C2.5 (scaling + envelope
domination), so nothing else is lost.

## Result

- Theorems (Laplace/OneD/TaylorPackage.lean, ~275 lines, zero
  sorries, zero warnings; gate verified via import + .olean):
  exists_stabilizer_envelope (C2.2: the coefficient-wise d with
  global envelope (a/2)x² ≤ stabilized polynomial, case split at
  |x| = ρ = min(1, a/(2(B+1))), no suprema), abs_moment_scaling
  (C2.3: exact q^{k+1} scaling of absolute moments under t·q² = 1),
  and tail_integral_le (C2.5: outside radius r the tail is bounded by
  e^{-(t/2)ρr²} times a full half-scale Gaussian moment — the
  superpolynomial prefactor for the moving split, via
  setIntegral_mono_on + setIntegral_le_integral).
- Surprises: (1) the two-region envelope proof formalized exactly per
  the consult's recipe, with nlinarith closing both regional
  assemblies once the per-term bounds were explicit; (2) monotone
  chains under exp are more robust as explicit
  mul_le_mul_of_nonneg_left haves + linarith than as nlinarith with
  hint lists; (3) rw direction discipline: Finset.sum_mul/sum_div
  needed ← forms since the sum lives on the LHS.
