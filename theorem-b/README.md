# Hurwitz's problem from Anthropic's Theorem B, in Lean 4

Draft, October 2026; feedback welcome. Not affiliated with Anthropic or OpenAI.

Anthropic's Theorem B (Appendix B of
[A 2^o(n) Time Algorithm for 3-SAT](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth),
October 2026) implies the bounds below. All are proved here in Lean 4, end to end, on top of
Anthropic's own Lean formalization.

| Theorem | Statement |
| --- | --- |
| `TheoremB.hurwitz_le_rpow` | For every ε > 0 and all large N, (X₁² + ⋯ + X_N²)(Y₁² + ⋯ + Y_N²) is a sum of at most N^(√2+ε) squares of complex bilinear forms. The best previous bound is Hrubeš's O(N^1.62) ([CCC 2024](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2024.12)). |
| `TheoremB.p_le_rpow` | For every ε > 0 and all large N, P(N) ≤ N^(√2+ε) over ℚ. P(N) is the least number of functions, each g(x,y)·g′(u,v) or g(x,u)·g′(y,v), that sum to the crossing [x = v][y = u] on N letters ([Naslund](https://arxiv.org/abs/1701.04475), Problem 12). This bound and the one above were stated independently on 27 October 2026, without a machine check, by Vaibhav Tulsyan ([eth-hamiltonicity](https://github.com/xennygrimmato/eth-hamiltonicity), `research/pieces.md` §2.2). |
| `TheoremB.hurwitz_le`, `TheoremB.p_le` | The same with explicit factors, for every N ≥ 2: P(N) ≤ (2N)^√2 · (2 log₂ N + 2)^(3c/2), and twice that for the squares, where c is Theorem B's constant. |
| `TheoremB.CharP.hurwitz_le_rpow` | For every odd prime p and ε > 0 there is N₀ such that, over every field of characteristic p and for all N ≥ N₀, (X₁² + ⋯ + X_N²)(Y₁² + ⋯ + Y_N²) is a sum of at most N^(√2+ε) squares of bilinear forms. Hrubeš proves O(N^1.62) over every field of positive characteristic. |
| `TheoremB.CharP.plef_rpow` | For every prime p and ε > 0, P_K(N) ≤ N^(√2+ε) for all large N, uniformly over the fields K of characteristic p. |
| `TheoremB.Rect.hurwitzR_exp_le` | Two lengths: for every ε > 0 there is a C such that, for all N₁, N₂ ≥ 1, (X₁² + ⋯ + X_{N₁}²)(Y₁² + ⋯ + Y_{N₂}²) is a sum of at most exp(√(ln²N₁ + ln²N₂) + ε·(ln N₁ + ln N₂) + C) squares of complex bilinear forms, a composition formula of type [N₁, N₂, M]. On the diagonal N₁ = N₂ this is N^(√2+2ε) (`TheoremB.Rect.hurwitzR_diag`). First stated, without a machine check, by Vaibhav Tulsyan ([eth-hamiltonicity](https://github.com/xennygrimmato/eth-hamiltonicity), `research/pieces.md` §2.3). |
| `TheoremB.Rect.pler_exp_le`, `TheoremB.Rect.pler_le` | The same bound for the crossing [x = v][y = u] with x, v among N₁ letters and y, u among N₂, over ℚ; explicitly, if N₁ ≤ p(h) and N₂ ≤ p(E), at most (2(E+h)+1)(2h+1)·C(E+h) terms, where C(m) = p(0) + ⋯ + p(m). |
| `TheoremB.pt_rank_le_rpow` | For every ε > 0 there is n₀ such that, over every field of characteristic 0, for all n ≥ n₀ and m ≥ 1, the identity matrix on (Fin n)^(2m) has partial-transpose rank at most n^((√2+ε)·m), that is n^(d(1/√2+ε/2)) for d = 2m factors. Rossman and Zhu ([arXiv:2512.01227](https://arxiv.org/abs/2512.01227), Proposition 6.1) derive n^(0.81d+O(1)) from Hrubeš's bound. `TheoremB.pt_rank_le` gives the explicit form. |

The argument has three steps. Theorem B's pieces, each expanded in its cheaper direction, decompose
the crossing; this is the argument Anthropic's paper uses for its Lemma 2 (Appendix G). Each term
then gives one product of two bilinear forms (Lemma 3.5 and Proposition 4.1(1) of
[Hrubeš, Wigderson and Yehudayoff 2011](https://www.math.ias.edu/~avi/PUBLICATIONS/Hrubes_Wi_Ye_2011.pdf),
proved here directly). Over ℂ each product is two squares. For partial-transpose rank, the
two-factor case is P(N) itself after renaming u and v, and grouping 2m coordinates into two halves
reduces 2m factors to two, as in Rossman and Zhu's proof of their Proposition 6.1.

In characteristic p, Theorem B's normalization divides by h!, which vanishes once h ≥ p. Anthropic's
Lean development proves the identities behind the pieces for integer matrices before that division
(`GeneralPieces.Series.sum_Qk_of`, `Qk_eq_Qk'_of`). Read modulo p, every operator maps the monomials
with a part divisible by p, or a part repeated p or more times, into themselves (`op_dvd`), so both
factorizations may drop them; for the monomials that remain, z_ν = ∏ k^(m_k)·m_k! is invertible and
replaces h!. The remaining monomials are counted by a finite product, compared with an integral; its
growth constant is not computed, because it cancels between the alphabet and the pieces. When p is
odd, −1 = a² + b² in 𝔽_p, so each product of two forms is three squares.

For two lengths, Lemma 9 of Appendix B holds on V_E for every weight E, and the same integer
identities hold for monomials of any weight. So the pieces with labels x, v of weight h and vectors
y, u of weight E add up to the crossing on p(h) × p(E) letters, and factor row-wise and
column-wise through monomials of weight at most E + h. Anthropic's development also proves
p(E) ≤ e^(c√E) and p(E) ≥ H·e^(c√E)/E^B with the same constant c = π√(2/3)
(`ClauseBound.Part.p_le_exp`, `ClauseBound.Part.exists_le_p`). Taking h and E least with
N₁ ≤ p(h) and N₂ ≤ p(E) gives c√h ≤ ln N₁ + O(log h), and then
c√(E + h) = √((c√h)² + (c√E)²) ≤ √(ln²N₁ + ln²N₂) + o(ln N₁ + ln N₂).

## Files

| File | Contents |
| --- | --- |
| `TheoremB/Defs.lean` | The definitions the theorems are stated in: `PLE` (P(N) ≤ M over ℚ), `PLEF` (the same over any commutative ring), `bil` (a bilinear form), `ProdLE` and `SOSLE` (a composition formula with M products or M squares), `mix` and `PTLE` (the identity matrix has partial-transpose rank at most M), and for two alphabets `PLER`, `bilR`, `ProdLER` and `SOSLER`. Imports Mathlib only. |
| `TheoremB/Corollaries.lean` | The proofs, from Anthropic's Theorem B. |
| `TheoremB/PTRank.lean` | The partial-transpose rank bounds, from `p_le` and `p_le_rpow`. |
| `TheoremB/CharP.lean` | Characteristic p, the algebra: the operators modulo p, the pairing, both factorizations of a piece, and the count of terms for one alphabet. |
| `TheoremB/CharPGrowth.lean` | Characteristic p, the growth of the surviving partitions, and the bounds for P and for sums of squares. |
| `TheoremB/Rectangular.lean` | Two alphabets: the pieces with labels of weight h and vectors of weight E, the count of terms, and the bounds for P(N₁, N₂) and for [N₁, N₂, M] formulas over ℂ. |
| `TheoremB/Sanity.lean` | Checks that the definitions mean what they say (below). |
| `scripts/PrintAxioms.lean` | Prints the axioms behind the main theorems, by name. |
| `scripts/CheckAxioms.lean` | The axiom gate: fails unless every constant in every `TheoremB` module depends only on the three standard axioms. |

## What a reader has to trust

The Lean 4 kernel, Mathlib, and the 80 lines of `TheoremB/Defs.lean`. The theorem statements use
only those definitions. Theorem B enters only through the proofs: as Anthropic's
`PiecesCounted.halfPiecesExist` and `PiecesCounted.toPure` in characteristic 0, and in
characteristic p as `GeneralPieces.Series.sum_Qk_of`, `GeneralPieces.Series.Qk_eq_Qk'_of`,
`AppHalfPieces.stExpansion` and `AppHalfPieces.lemmaDual`. The two-alphabet bounds use the same
four, with `ClauseBound.Boson.Half.Qk_eq` and the partition bounds `ClauseBound.Part.p_le_exp` and
`ClauseBound.Part.exists_le_p`.

`TheoremB/Sanity.lean` checks that the definitions encode the classical problems and are not
satisfied trivially:

- `sos_two`: the two-square identity (a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)² is a formula of
  type [2, 2, 2] in the sense of `SOSLE`.
- `sos_trivial`, `ple_trivial`: the trivial bounds, N² squares and N² terms, which the main theorems
  improve on.
- `not_sos_one_zero`, `not_ple_one_zero`: zero terms never suffice.
- `ptle_trivial`, `not_ptle_zero`: for `PTLE`, the trivial bound n^d holds, and zero terms never
  suffice.
- `plef_trivial`, `not_plef_one_zero`: for `PLEF`, the trivial bound N² holds over every commutative
  ring, and zero terms never suffice once 1 ≠ 0.
- `sos_two_zmod3`: over 𝔽₃ the two-square identity is a formula of type [2, 2, 2].
- `sosR_trivial`, `pler_trivial`, `not_sosR_one_zero`, `not_pler_one_zero`: for the two-alphabet
  definitions, the trivial bounds N₁N₂ hold, and zero terms never suffice.

## Build

This is a separate Lake project inside the repository; run these commands from `theorem-b/`. Needs
[elan](https://github.com/leanprover/elan), about 10 GB of disk and 8 GB of memory.

```sh
lake exe cache get
lake build
lake env lean scripts/CheckAxioms.lean
lake env lean scripts/PrintAxioms.lean
```

`lake build` fetches Anthropic's formalization (anthropics/formal-math, pinned to commit
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, directory `eth`) and builds the parts of it this
project imports. `scripts/CheckAxioms.lean` reads the compiled environment and fails if any
constant declared in a `TheoremB` module, including private and auxiliary ones, depends on an axiom
other than `propext`, `Classical.choice` and `Quot.sound` (`sorryAx` included), or if a file under
`TheoremB/` is not checked. `scripts/PrintAxioms.lean` prints the same for the main theorems by name.

## Checks run

In this repository, on October 29, 2026, 4:13 to 4:52 p.m. Eastern (records, with source and log hashes, in
`../validation/theorem-b/`): `lake build`; `scripts/PrintAxioms.lean`, 51 theorems; `scripts/CheckAxioms.lean`,
312 constants; `lake env leanchecker` on each of the seven modules; and `lake env leanchecker --fresh` on each
of the seven modules. All pass, each theorem and constant depending only on `propext`, `Classical.choice` and
`Quot.sound`.

Earlier runs, October 27 and 28, 2026:

- `lake build` succeeds with no errors or warnings under `autoImplicit = false`, as in Anthropic's
  lakefile. In a new directory, fetching the dependencies and building took about 4 minutes before
  the characteristic-p files were added.
- `lake env lean scripts/PrintAxioms.lean`: all 51 theorems depend only on `propext`,
  `Classical.choice` and `Quot.sound`.
- `lake env lean scripts/CheckAxioms.lean`: all 312 constants of the 7 `TheoremB` modules depend
  only on those three. Tested to fail on a `sorry`, on a new axiom and on an unimported file.
- `lake env leanchecker` on each of `TheoremB.Defs`, `TheoremB.Corollaries`, `TheoremB.PTRank`,
  `TheoremB.CharP`, `TheoremB.CharPGrowth`, `TheoremB.Rectangular` and `TheoremB.Sanity`: re-runs
  the kernel on every declaration in the seven files. All pass.
- `lake env leanchecker --fresh` on `TheoremB.Corollaries`, `TheoremB.PTRank` and
  `TheoremB.Sanity`: replay every constant each file depends on, including Lean's core library,
  Mathlib and Anthropic's Theorem B development, into an empty environment and check each with the
  kernel. All pass, in about 6, 6 and 4 minutes. The `PTRank` replay includes the theorems of
  `Corollaries` it uses.
- `lake env leanchecker --fresh` on `TheoremB.CharPGrowth` and `TheoremB.Sanity` after the
  characteristic-p files were added: both pass, in about 5 and 3½ minutes. The `CharPGrowth` replay
  includes the theorems of `CharP` it uses and the parts of Anthropic's development behind them.
- `lake env leanchecker --fresh` on `TheoremB.Rectangular` and `TheoremB.Sanity` after the
  two-alphabet files were added: both pass, in about 6 and 4¼ minutes. The `Rectangular` replay
  includes the theorems of `CharP` it uses, Anthropic's partition bounds and the parts of the
  development behind them.

`leanchecker` uses Lean's own kernel, so it detects tampering with the environment but is not an
independent implementation. No external checker, such as lean4lean or nanoda, has been run.

## Limits

- Characteristic 2: the bound on P holds, but the sum-of-squares question is trivial there, since
  (Σ X_i²)(Σ Y_j²) = ((Σ X_i)(Σ Y_j))².
- Not over ℝ: turning a product into squares needs −1 to be a sum of squares. Over ℝ the best known
  bound is still O(N²/log N).
- In characteristic p the bounds are asymptotic only, with no explicit N₀.
- Asymptotic only: with the piece sizes in Anthropic's Lean statement of Theorem B, rounded up to
  powers of two, the bound first beats N^1.62 at N = 2^73 (2^78 for the squares). That comparison
  was computed, not checked in Lean.
- Not formalized here: the consequences for non-commutative circuits, in any characteristic (through
  Hrubeš's Section 6 and fast matrix multiplication), Rossman and Zhu's Theorem 6.6 for ordered branching programs,
  and the iterated partial-transpose bound over ℂ.

## Credit and use of AI

The mathematics is a corollary of Anthropic's Theorem B, using an argument from Anthropic's paper and
one from Hrubeš, Wigderson and Yehudayoff. This repository applies them to Theorem B and checks the
chain in Lean. Vaibhav Tulsyan, in
[github.com/xennygrimmato/eth-hamiltonicity](https://github.com/xennygrimmato/eth-hamiltonicity),
independently stated the square bounds P(N) ≤ N^(√2+o(1)) and σ_ℂ(N) ≤ N^(√2+o(1)) on 27 October
2026, the day this repository's first version was written (`research/pieces.md` §2.2, without a
machine check). Tulsyan also first stated the two-length bound, [n₁, n₂, s] formulas with
s ≤ 2^(√(λ₁² + λ₂²) + o(λ)) where n_i = 2^(λ_i) (§2.3, without a machine check);
`TheoremB/Rectangular.lean` checks it. The work was done with AI assistance: Claude (Anthropic) and
ChatGPT (OpenAI) were used to find and check the argument, write the Lean proofs, and search the
literature. Corrections are welcome.

## License

Apache License 2.0; see `LICENSE`. Copyright 2026 Carson Weitnauer. Anthropic's formal-math, used
here as a dependency, is also Apache-2.0.
