# JSP-000216 formalization submission record

**Submission status:** progress record for public review. This document does not
claim a complete solution or award eligibility.

## Problem

- **Catalog problem:** [JSP-000216](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000216)
- **Mathematical source:** [Erdős Problem 245](https://www.erdosproblems.com/245)
- **Problem:** If `A ⊆ ℕ` is infinite and has asymptotic density zero, prove
  that

  ```text
  limsup_N |(A + A) ∩ [1,N]| / |A ∩ [1,N]| ≥ 3.
  ```

The catalog lists the result as solved, with references to Mann (1960) and
Freiman (1973). The historical mathematical result and this Lean
formalization are separate contributions.

## Public proof repository

The source repository is:

<https://github.com/ddddddfsd/sunprize-lean-jsp-000216>

The submitted branch is `main`. The exact 40-character SHA for any public
submission is the value returned by `git rev-parse HEAD` after the reviewed
commit has been pushed. A complete-proof catalog submission must pin that SHA
and must use a later commit than this progress record.

## Formalization correspondence

The core file is [`JSP000216.lean`](JSP000216.lean), in namespace
`JSP000216`. It defines:

- `NatSet`, `Infinite`, `SumSet`, `countPos`, and `ZeroDensity`;
- set-inclusion monotonicity for `countPos` and `ZeroDensity`;
- the discrete approximation interface `DiscreteThreeApprox`;
- monotonicity of `DiscreteThreeApprox` in its reciprocal-error parameter;
- simultaneous large sparse cutoffs from `Infinite` plus `ZeroDensity`;
- unbounded positive counting of the sumset along even cutoffs;
- value-unbounded positive truncation counts for every infinite set;
- a zero-density contradiction for any recurrent linear endpoint bound
  `N ≤ C * countPos A N + D`;
- the equivalent eventual lower-bound form
  `zeroDensity_eventually_exceeds_linear_bound`;
- the corresponding member-endpoint form, for structural arguments that
  return a recurrent bound at actual elements of `A`;
- the combined small-sumset endpoint contradiction: recurrent prefixes with
  `|F+F| ≤ 3|F|−4` and endpoint length `|F+F|−|F|+1` are incompatible with
  infinite zero density (`zeroDensity_not_recurrent_small_sum_endpoint`);
- the `GapSparseThreeApprox` witness interface and its implication to
  `DiscreteThreeApprox`;
- the catalogue-shaped target interface `DiscreteErdos245`;
- finite witness and counting lemmas for `2*n - 1` sums; and
- a finite three-block construction yielding `3*n - 1` witnesses under an
  explicit gap hypothesis.

The `mathlib/` subproject adds a checked `Set`/`Filter`/`EReal` bridge from the
reciprocal-error interface to the exact limsup conclusion, together with the
finite diameter-to-progression covering lemma. It does not include the finite
Freiman `3k−4` inverse theorem or a proved infinite zero-density transfer;
the finite theorem is exposed as a separately audited external axiom.
It also checks the primitive consequence that any positive-step cover of a
finite set with trivial common difference divisor has unit step and therefore
length at least the endpoint diameter.

The same subproject now proves the endpoint lower bound
`2 * F.card - 1 ≤ (F + F).card` for nonempty finite integer sets, and an
integer small-doubling bound: if the doubling is at most `2 - ε` with
`0 < ε ≤ 1`, then `F.card ≤ 2 / ε - 1`. These are verified finite-side
lemmas; they do not supply the missing `3k−4` inverse theorem.

The axiom-assisted entry now proves `discreteErdos245_external` from two
explicit external assumptions: `freiman_3k4_inverse_external` for the finite
inverse theorem and `freiman_zero_density_transfer_external` for the infinite
scale transfer. These assumptions are intentionally visible in the axiom
audit; the result is not a kernel-only proof of the historical theorem.

## Reproduction

The project pins Lean 4.33.0 in `lean-toolchain` and has no external Lake
packages. From the repository root:

```powershell
lake build
cd mathlib
lake env lean BridgeExact.lean
lake env lean FreimanProgression.lean
lake env lean IntegerSmallDoubling.lean
```

The build is expected to finish successfully for the current core layer.
The proof file can also be checked directly with the Lean executable selected
by the pinned toolchain.

## Trust and audit status

The proved bridge lemmas contain no `sorry` or `admit` and audit to the
standard Lean kernel set `[propext, Classical.choice, Quot.sound]`. The
axiom-assisted target additionally depends on the two explicitly named
external assumptions above. It is therefore suitable as an assumption-
carrying formal record, not as a kernel-only award proof.

## Outstanding work

The following items are required before this becomes an award submission:

1. Replace `freiman_3k4_inverse_external` with a kernel-checked finite proof.
2. Replace `freiman_zero_density_transfer_external` with a kernel-checked
   infinite transfer proof.
3. Re-run the complete audit on the exact public commit after removing the
   external assumptions.
