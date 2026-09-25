# Mathlib verification layer

This subproject contains the independently checked bridges needed to connect the
core JSP-000216 development to the exact Formal Conjectures statement.

- `BridgeExact.lean` proves the reciprocal-error `SetApprox` hypothesis implies
  the exact `EReal` `atTop.limsup` lower bound, including eventual denominator
  positivity and the real-index transport.
- `FreimanProgression.lean` proves the finite diameter-to-unit-progression
  covering lemma for finite integer sets.

Both files are free of `sorry`, `admit`, and custom axioms. These files do not
claim the missing finite Freiman `3k-4` inverse theorem or its infinite
zero-density transfer; those are the remaining mathematical steps.

From this directory, with Mathlib `v4.33.1` available:

```powershell
lake env lean BridgeExact.lean
lake env lean FreimanProgression.lean
```
