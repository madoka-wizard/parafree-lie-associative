## Source and license

These files are a compatibility port from leanprover-community/mathlib4,
commit `c7780ed427bbed31ee0c430a5594ed5ea4c7d5b5`, the inspected head of
[PR #34913](https://github.com/leanprover-community/mathlib4/pull/34913).
They retain the upstream declaration namespaces because the project's pinned
Mathlib does not contain these declarations. The dependency pins are unchanged.

| Local file | Original source at the pinned commit |
| --- | --- |
| `ExteriorAlgebraProduct.lean` | `Mathlib/LinearAlgebra/ExteriorAlgebra/Product.lean`, plus the two anticommutation lemmas from `ExteriorAlgebra/Basic.lean` |
| `ExteriorBaseChange.lean` | `Mathlib/LinearAlgebra/ExteriorPower/BaseChange.lean` |
| `ExteriorPowerProduct.lean` | `Mathlib/LinearAlgebra/ExteriorPower/Product.lean` |
| `Complex.lean` | `Mathlib/RingTheory/KoszulComplex/Complex.lean` |

Copyright notices are retained in the source files. The additional
`ExteriorAlgebra/Basic.lean` source carries Copyright (c) 2020 Adam Topaz;
authors Zhangir Azerbayev, Adam Topaz, and Eric Wieser. All these sources are
released under the Apache License, Version 2.0; see [LICENSE](LICENSE).

## Local adaptations

The port targets Lean 4.29.0 and Mathlib
`8a178386ffc0f5fef0b77738bb5449d50efeea95`. Imports are redirected within this
directory. Compatibility edits replace newer chain-map constructors and tactic
syntax, give explicit injectivity and exterior-dimension proofs, add the
exterior-map coercion lemma, and resolve an equivalence simplification. The
upstream files locally retain Mathlib's implicit-variable options; the rest of
the project continues to disable automatic implicit variables.

The exactness induction is strengthened to
`koszulComplex.exactAt_of_isWeaklyRegular`: nontriviality of the final quotient
is unnecessary for positive-degree exactness. The original regular-sequence
statement remains available as a corollary. This strengthening is proved by the
same induction, using the checked long exact homology sequence and the computed
connecting map, with no extra hypothesis about homology.

The application to arbitrary sets of polynomial variables lives separately in
`Parafree/Homology/Koszul`, and finite exterior support is proved separately in
`Parafree/Linear/ExteriorFiniteSupport.lean`.

Only the listed dependency closure was ported. No other declarations from the
pull request or from the separate KoszulComplex repository are imported.
