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
- the corresponding member-endpoint form, for structural arguments that
  return a recurrent bound at actual elements of `A`;
- the `GapSparseThreeApprox` witness interface and its implication to
  `DiscreteThreeApprox`;
- the catalogue-shaped target interface `DiscreteErdos245`;
- finite witness and counting lemmas for `2*n - 1` sums; and
- a finite three-block construction yielding `3*n - 1` witnesses under an
  explicit gap hypothesis.

The `mathlib/` subproject adds a checked `Set`/`Filter`/`EReal` bridge from the
reciprocal-error interface to the exact limsup conclusion, together with the
finite diameter-to-progression covering lemma. It does not include the finite
Freiman `3k−4` inverse theorem or the infinite zero-density transfer.
It also checks the primitive consequence that any positive-step cover of a
finite set with trivial common difference divisor has unit step and therefore
length at least the endpoint diameter.

The same subproject now proves the endpoint lower bound
`2 * F.card - 1 ≤ (F + F).card` for nonempty finite integer sets, and an
integer small-doubling bound: if the doubling is at most `2 - ε` with
`0 < ε ≤ 1`, then `F.card ≤ 2 / ε - 1`. These are verified finite-side
lemmas; they do not supply the missing `3k−4` inverse theorem.

`DiscreteErdos245` is currently a definition, not a proved theorem. The
Mathlib bridge for the reciprocal-error interface is checked in `mathlib/`,
but the finite-to-infinite theorem that supplies its hypothesis has not yet
been formalized.

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

The current core layer contains no `sorry`, `admit`, or custom axioms. It is a
finite/interface layer and does not establish the original theorem. A final
catalog submission will require a clean build at a fixed commit, a complete
statement-to-proof correspondence, and an axiom audit for the fully qualified
target theorem. The newly added core lemmas were audited with `#print axioms`;
their dependency set is the standard Lean kernel set
`[propext, Classical.choice, Quot.sound]` and contains no `sorryAx`.

## Outstanding work

The following items are required before this becomes an award submission:

1. Formalize the finite Freiman structural theorem or provide a complete
   independently checkable proof dependency.
2. Prove the infinite transfer from the finite structure to the zero-density
   limsup bound for every admissible `A`.
3. Formalize the finite `3k−4` inverse theorem and the infinite transfer from
   zero density to the reciprocal-error interface.
4. Re-run the complete audit on the exact public commit and then prepare a
   catalog-only PR following the award repository's template.
