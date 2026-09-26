# Mathlib verification layer

This subproject contains the independently checked bridges needed to connect the
core JSP-000216 development to the exact Formal Conjectures statement.

- `BridgeExact.lean` proves the reciprocal-error `SetApprox` hypothesis implies
  the exact `EReal` `atTop.limsup` lower bound, including eventual denominator
  positivity and the real-index transport.
- `FreimanProgression.lean` proves the finite diameter-to-unit-progression
  covering lemma for finite integer sets. It also proves that a positive-step
  cover of a primitive finite set must have unit step, hence its length is at
  least the endpoint diameter, and proves the elementary endpoint lower bound
  `2 * |F| - 1 ≤ |F + F|` for every nonempty finite integer set.
- `IntegerSmallDoubling.lean` proves an integer specialization of the
  Mathlib small-doubling coset-cover theorem: if a nonempty finite integer
  set has doubling at most `2 - ε`, then its cardinality is at most
  `2 / ε - 1`. It also records the numerical diameter consequence of a
  primitive progression cover whose length is bounded by the sumset excess.

The proved lemmas in these files are free of `sorry` and `admit`. The finite
Freiman `3k-4` inverse theorem is additionally exposed as the explicit axiom
`FreimanProgression.freiman_3k4_inverse_external`; the core project exposes
the infinite zero-density transfer as a separate named axiom. The resulting
target is therefore assumption-carrying, and its axiom audit makes those two
dependencies visible.

From this directory, with Mathlib `v4.33.1` available:

```powershell
lake env lean BridgeExact.lean
lake env lean FreimanProgression.lean
lake env lean IntegerSmallDoubling.lean
```
