# Noncommutative circuits for the identity polynomial

Lean 4 proofs that Hrubeš's identity polynomial ID_N = Σ_{i,j ≤ N} x_i y_j x_i y_j, the noncommutative
elementary symmetric polynomial S_{4,N} and the rectangular permanent perm_{4,N} have noncommutative
arithmetic circuits of size O(N^(1.6692+ε)) for every ε > 0, over every field of characteristic other than 2.
The previous published bound is O(N^1.96) (Hrubeš).

The paper is [`paper/main.pdf`](paper/main.pdf) (source `paper/main.tex`). Everything it states as a theorem
or lemma is proved here, using only Lean's axioms `propext`, `Classical.choice` and `Quot.sound`.

## Results

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem 1.1 | `IDMM.id_bound_every_char` | Over every field `F : Type u` with `ringChar F ≠ 2`: `IDBoundF`, `S4BoundF` and `Perm4BoundF` at exponent `4173/2500 = 1.6692`. |
| Theorem 1.2 | `IDMM.main_target`, `IDMM.main_target_char_zero`, `IDMM.main_target_almost_every_char` | Exponent `211321/125000 = 1.690568` from OpenAI's rectangular bounds: over ℂ, over every field of characteristic 0, and outside a finite (uncomputed) set of characteristics. |
| Theorem 1.3 | `PauliCubes.id_circuit`, `PauliCubes.s4_circuit`, `PauliCubes.perm4_circuit` | Exponent `1.727899` without fast matrix multiplication, every field of characteristic other than 2. |
| Theorem 1.4 | `IDMM.construction_gen`, `IDMM.construction_target` | The construction: block oracles of cost `(2^m)^(w+ε)` give exponent `2H(1/4) − 2μH(1/(4μ)) + μw`. |
| Theorem 7.8 | `IDMM.construction_almost_every_char`, `IDMM.construction_char_zero` | Field transfer for any complex-admissible `w`. |
| (background) | `theorem-b/` | Sums of squares: (X₁² + ⋯ + X_N²)(Y₁² + ⋯ + Y_N²) is a sum of N^(√2+o(1)) squares of bilinear forms, from Anthropic's Theorem B. See [`theorem-b/README.md`](theorem-b/README.md). |

The circuit model (`PauliCubes/CircuitDefs.lean`) and the bound statements (`IDMM/Eventual.lean`) are the
definitions to read; Section 8 of the paper compares them with Hrubeš's.

## Checks on the circuit model

`IDMM/CircuitModel.lean`, `IDMM/StrictMain.lean`, `IDMM/StrictEveryChar.lean`:

| Check | Lean | Statement |
| --- | --- | --- |
| Hrubeš's model, read strictly | `IDMM.StrictNCSizeLE` | Every non-input node is the sum or product of two *different* earlier nodes. |
| Conversion | `IDMM.ncSizeLE_strict` | A circuit with `s` nodes gives a strict one with at most `2s + 1` nodes. |
| The strict model is stronger | `IDMM.StrictNCSizeLE.ncSizeLE` | Every strict circuit is a circuit. |
| Theorems 1.1–1.3, strict | `IDMM.strict_id_bound_every_char`, `IDMM.strict_main_target`, `IDMM.strict_main_target_char_zero`, `IDMM.strict_main_target_almost_every_char`, `IDMM.strict_cubes_bound` | The same exponents in the strict model. |
| Not vacuous: lower bound | `IDMM.two_mul_le_of_ncSizeLE_ID` | Every circuit computing `ID_N` has at least `2N` nodes. |
| Not vacuous: bound predicate | `IDMM.not_idBoundF_of_lt_one`, `IDMM.not_strictIDBoundF_of_lt_one` | No exponent below 1 is achievable, in either model. |
| Not vacuous: hypotheses | `IDMM.id_bound_every_char_rat`, `IDMM.id_bound_every_char_zmod3` | Theorem 1.1 over ℚ and over `ZMod 3`. |

## How the 1.6692 proof goes

`IDMM/EveryChar.lean`:

1. Uznański's rectangular bound ω(1,k,1) ≤ 1 + k + 1/(4k), in Zhou and Wang's integer form
   (`Matmul.RectangularRankBridge.exists_scheme_certificate`), gives at aspect k = 11/18 one integer rank
   decomposition of a matrix tensor ⟨a, b, a⟩ with rank exponent below 200/99 + 10⁻⁵.
2. `rankAtMost_of_scheme` maps it into any commutative ring, so every characteristic is covered at once.
3. Over `F(√−1)`, `oracles_of_scheme` turns it into block oracles and `construction_gen` gives the bound at
   μ = 18/29; `IDBoundF.of_ext` brings it down to `F`.
4. `uz_exponent_slack` certifies C(18/29, 200/99) + 10⁻⁵ < 1.6692, where C = 1.66916842….

The construction itself (Sections 3–6 of the paper) is in `IDMM/Maj*.lean`, `Corner.lean`,
`BlockAssembly.lean`, `BlockCover.lean`, `Layout.lean`, `MajCircuit.lean` and `Construction.lean`.
Comments there cite "cycle 055", the research note in which the construction was first worked out; it is not
included. Its §1 is Section 3 of the paper (the corner sum of squares), §2 is Section 4 (Majorana blocks), §3 is
Section 5 (covering), and §§4–5 are the block evaluation and assembly (Proposition 4.3 and Section 6).

## Layout

| Path | Contents |
| --- | --- |
| `IDMM/` | This development: the construction, both matrix-multiplication routes, field transfer. |
| `PauliCubes/` | The Pauli-cube bound (Theorem 1.3), Hrubeš's Lemma 22, the circuit model and the reductions for S_{4,N} and perm_{4,N}. |
| `Matmul/` | Zhou and Wang's formalization of Uznański's bound (64 files). |
| `OAI/` | OpenAI's matrix-multiplication library (509 files, unchanged). |
| `theorem-b/` | A separate Lake project (Lean 4.33.1, on Anthropic's formalization): the √2 sum-of-squares bounds. |
| `paper/` | The paper. |
| `scripts/`, `validation/` | The verification runner, the audit, and the records of the checks. |

`Matmul` and OpenAI's `OAI.LinearAlgebra.MatrixMultiplication.Main` declare some of the same names, so they
cannot be imported into one file. Theorem 1.1 is checked in one import closure (`IDMM.FinalAuditEveryChar`)
and Theorem 1.2 in another (`IDMM.FinalAudit`); see `Matmul/PORTING.md`.

## Build and verify

Needs [elan](https://github.com/leanprover/elan), about 15 GB of disk and 8 GB of memory.

```sh
lake exe cache get
git -C .lake/packages/fixed-point-theorems apply ../../../fixed-point-theorems-lean4341.patch
lake build
python3 scripts/validate.py --out validation/release
python3 scripts/audit.py
```

The patch is OpenAI's, unchanged from `openai/math` (`lean/patches`); it adapts harfe's fixed-point package to
this toolchain. `validate.py` runs the full build, prints the signatures and axioms of the top-level theorems
of both import closures (`IDMM/FinalAudit.lean`, `IDMM/FinalAuditEveryChar.lean`), and replays both modules
and everything they import in a fresh kernel environment (`leanchecker --fresh`). It records commands, exit
codes, timestamps and the SHA-256 of every Lean source, pin file and log. `audit.py` checks a record against
the sources in the repository, checks that the logs give the signature and axiom list of every audited theorem,
checks that OpenAI's and Zhou and Wang's files match upstream
(`validation/provenance.json`), and scans `IDMM`, `PauliCubes` and `Matmul` for `sorry`, `native_decide` and
added axioms.

`validation/release/` is the record for the sources in this repository (October 29, 2026, Eastern time), and
`validation/theorem-b/` is the record for `theorem-b/`. `theorem-b/README.md` has that project's own build
steps.

## Attribution and licenses

- `OAI/`: 509 unchanged files from [openai/math](https://github.com/openai/math) commit `7ef5c0c`
  (Apache-2.0, `LICENSE-OPENAI`).
- `Matmul/`: Yang Zhou and Mingsheng Wang,
  [rectangular-matmul-rings](https://github.com/Hugin-Hilbert/rectangular-matmul-rings) commit `285f513`
  (Apache-2.0, `Matmul/LICENSE`, `Matmul/NOTICE`), formalizing Przemysław Uznański's bound
  ([arXiv:2610.10494](https://arxiv.org/abs/2610.10494)). One file differs, by two added binders and a change
  notice; see `Matmul/PORTING.md`.
- `fixed-point-theorems-lean4341.patch`: OpenAI's patch of harfe's
  [fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4) (MIT,
  `LICENSE-FIXED-POINT-THEOREMS`).
- `theorem-b/` builds on Anthropic's [formal-math](https://github.com/anthropics/formal-math) `eth`
  development, pinned and unchanged.
- `IDMM/`, `PauliCubes/`, `theorem-b/`, `paper/` and the scripts: Apache-2.0 (`LICENSE`; `LICENSE-PAULICUBES`
  is the same license).

The mathematics, the Lean proofs and the paper were produced by AI systems (OpenAI's Codex and Anthropic's Claude).
Carson Weitnauer supervised the research and is responsible for its release. How to attribute authorship of such
work is an open question. The paper's AI-use statement gives the details.
