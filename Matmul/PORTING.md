# Port of Hugin-Hilbert `Matmul` to Lean 4.34.1

Source: github.com/Hugin-Hilbert/rectangular-matmul-rings, commit 285f513,
`formalization/Matmul/` (64 modules including `EntropyAnalytic/`), Apache-2.0.
Upstream built it with Lean 4.33.0-rc1 and Mathlib 79d0395, by calling `lean`
directly (no lakefile). Here it builds with Lean 4.34.1 and Mathlib d13f23b.

## What was copied

- `Matmul/**/*.lean`: all 64 modules, byte-identical except the two lines below and a three-line change
  notice at the top of `UniversalRecursiveProgram.lean` (Apache-2.0, section 4(b)).
- License notices, unchanged: `LICENSE` and `NOTICE` (repository root),
  `UPSTREAM-LICENSE` (from `formalization/`; `DiscreteSlopes.lean` cites it as
  `formalization/UPSTREAM-LICENSE`), and `licenses/omega-nine-quarters-all-fields.NOTICE`.
  `NOTICE` also cites `formalization/PROVENANCE.txt` and
  `formalization/FixedPointTheorems/MIT_LICENSE`. Those were not copied; see the
  upstream repository.

Not copied: upstream `OAI/`, `FixedPointTheorems/`, `Checks/`, and the Python
scripts. `Matmul` imports this project's `OAI/` (openai/math 7ef5c0c) and the
`fixed-point-theorems` package instead. The upstream `OAI/` files are backports.
They differ from ours only inside proofs (`if_pos`/`ite_eq_left`,
`setOf_forall`/`ofPred_forall`, one import path) and in their adaptation headers.
Upstream `Entropy/ConditionalContinuity.lean` is a 38-line excerpt.
`exists_rational_law_sequence` has the same statement and proof in our full file.

`lakefile.toml`: added `[[lean_lib]] name = "Matmul" globs = ["Matmul.+"]`
(not a default target).

## Changes (2)

| File | Line | Old → new | Reason |
|---|---|---|---|
| `UniversalRecursiveProgram.lean` | 46 | `def childWire (s : Fin ρ) …` → `def childWire {t : ℕ} (s : Fin ρ) …` | Upstream relied on Lean's default `autoImplicit = true`. This project sets `autoImplicit = false`. |
| `UniversalRecursiveProgram.lean` | 74 | `def encode {R : Type*} …` → `def encode {t : ℕ} {R : Type*} …` | Same. |

A scratch check confirmed both edits. The same text was elaborated with
`autoImplicit true`. Its types were `Expr.equal` (binder info included) to the
edited declarations, with the same universe parameters, and the two bodies were
proved equal. No statement or definition changed. Nothing else needed repair.
The upstream sources still give deprecation warnings (`if_pos`, `if_neg`,
`if_false`) and linter warnings, and these were left alone.

## Verified (2026-10-29)

- `lake build` succeeds on `Matmul.RectangularPrograms`, `Matmul.HomogeneousProfiles`,
  `Matmul.IntegerRankExponent` and `Matmul.EntropyAnalytic.AxiomAudit`, which
  together cover all 64 modules.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for
  `Matmul.RectangularRankBridge.exists_scheme_certificate`,
  `Matmul.RectangularPrograms.rectangular_multiplication_programs`, and
  `Matmul.RectangularPrograms.program_correct`.
- A grep of the sources finds no `sorry`, `admit`, `axiom`, `native_decide`,
  `implemented_by`, `extern`, `unsafe` or `#eval`. The only `#print axioms` lines
  are in `EntropyAnalytic/AxiomAudit.lean`.

## Known limitation: name clashes with `OAI.…AuxiliarySeparation`

Several `Matmul` modules declare names in `OAI.MatrixMultiplication.AuxiliarySeparation.*`.
These are integer-ring versions of the omega-nine-quarters modules: `IntegerTensor`,
`IntegerScalar`, `IntegerSemiring`, `IntegralTripling`, `IntegerRankExponent`,
and `EntropyAnalytic/Tag`. 377 of these constants (248 without auxiliary
`eq_`/`_proof`/`match_` constants) are also defined by this project's
`OAI/…/AuxiliarySeparation/` modules: `Tensor.{Semiring,Scalar,DirectSum,…}`,
`Sector.*`, `Arithmetic.RankExponent`, `Entropy.Tag`, `Character.Basic`, and
`Convolution.Basic`.

Because of these clashes, `Matmul` cannot be imported in the same file as those
modules. That includes `OAI.LinearAlgebra.MatrixMultiplication.Main`, which
imports `AuxiliarySeparation.Arithmetic.RankExponent`. Fixing it would need
`Matmul` declarations to be renamed or moved to another namespace, so it was
left as is. `Matmul.RectangularPrograms` does import cleanly next to the other
OAI modules that `IDMM` uses (`Arithmetic.Exponent`, `Tensor.ComplexMatrixTensor`,
`Arithmetic.RecursiveBlockPrograms`, `Rectangular.Growth`,
`Numerical.ComplexRationalLogCertificate`).
