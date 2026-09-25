# JSP-000216: Lean formalization workbench

This local repository is reserved for a prospective complete Lean formalization of [JSP-000216](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000216), corresponding to [Erdős Problem #245](https://www.erdosproblems.com/245). The mathematical result is due to G. A. Freiman (1973).

The proof is **not complete**. No public proof repository, catalog pull request, or award claim has been created. A successful build of a weaker statement or an example would not establish the original result.

## Local progress (2026-09-25)

[`JSP000216.lean`](JSP000216.lean) is a dependency-free Lean 4.33.0 core
layer. It defines unbounded subsets of `ℕ`, their additive sumsets, positive
interval counts, and a discrete zero-density interface. It proves the basic
counting and infinitude lemmas, and formalizes the finite additive-combinatorics
step that a strictly increasing sequence of length `n ≥ 2` yields `2*n - 1`
distinct pairwise sums. The latter is exposed through `HasDistinctWitnesses`,
so a later Mathlib layer can connect it to `Finset.card`.

The file now also defines `TruncatedSumSet` and proves that the same
`2*n−1` witnesses lie in the positive cutoff at `2*N` when the selected
sequence lies in `[1,N]`. Monotonicity under larger cutoffs and larger base
sets is proved at the witness level. From `Infinite A`, it can now extract an
arbitrary positive strictly increasing prefix and produce a corresponding
truncated witness automatically. A further counting lemma converts a strictly
increasing list of positive witnesses bounded by `N` into a lower bound on
`countPos`, yielding the explicit `2*n−1` sumset count at cutoff `2*N`.

The exact catalogue statement still requires the real-valued `Set`/`Filter`/
`EReal` formalisation and Freiman's analytic passage from finite sumset bounds
to the `limsup` lower bound 3. The core file uses reciprocal-error
approximations to 3 for its discrete interface; an exact integer inequality at
infinitely many cutoffs would be stronger than a real limsup statement. The
catalogue theorem is intentionally not represented by `sorry`, an `axiom`, or
a weaker theorem with the same name.

The current mathematical gap and the finite `3k−4` structural route are
recorded in [`ANALYSIS-216.md`](ANALYSIS-216.md).

## Reproducible build

The repository is a small Lake library project. With the pinned Lean 4.33.0
toolchain, run:

```powershell
lake build
```

This builds the `JSP000216` library target. With the bundled Lean executable,
the source can also be checked directly:

```powershell
$lean = 'C:\Users\Windows User\Documents\Codex\2026-09-25\https-github-com-thejustinsunprize-awards-tree\work\lean-toolchain\lean-4.33.0-windows\bin\lean.exe'
& $lean D:\Users\WindowsUser\Desktop\SunPrize-Lean\JSP000216.lean
```

The initial submission consists of the Lean source, the analysis note, this
README, the Lake configuration and the pinned toolchain file. Local handoff
notes, scratch work and build products are excluded from Git by `.gitignore`.
Before any public push, review the complete diff, dependency chain, provenance
and verification evidence. Any public attribution must distinguish the
historical mathematical solution, actual formalization contributions and AI
assistance truthfully.
