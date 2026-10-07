# Runs of multiples in a finite set

[![Lean Action CI](https://github.com/jas-ho/runs-of-multiples-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/jas-ho/runs-of-multiples-lean/actions/workflows/lean_action_ci.yml)

A Lean 4 + Mathlib formalization of the following result.

Let `S` be a set of `n` positive integers. For `a ∈ S`, let `k(a)` be the least positive integer `k` with `k · a ∉ S`. Then

  max over |S| = n of Σ_{a ∈ S} k(a) = Θ(n log n log log n).

The set `{1, …, n}` gives only `n log n + O(n)`; sets built from smooth numbers gain the extra `log log n` factor.

The repository contains two complete proofs of the same theorem, each with an informal write-up:

| Lean theorem | Upper bound | Lower bound | Informal proof |
|---|---|---|---|
| `RunsOfMultiples.main_theorem` | entropy chain rule along prime factorisations | smooth numbers `≤ X` and Rankin's estimate | [`docs/runs-of-multiples.pdf`](docs/runs-of-multiples.pdf) |
| `RunsOfMultiples.main_theorem_alt` | compression to a divisor-closed, prime-shift-closed set, then a bound on radicals | a box of small-prime exponents times a simplex of large-prime exponents | [`docs/first-missing-multiple.pdf`](docs/first-missing-multiple.pdf) |

Both theorems depend only on the standard axioms (`#print axioms` gives `[propext, Classical.choice, Quot.sound]`). There is no `sorry`, `admit`, `axiom` or `native_decide`.

[`docs/runs-of-multiples-rewrite.pdf`](docs/runs-of-multiples-rewrite.pdf) is a rewrite of the entropy write-up with the mathematics unchanged and the language revamped for readability. The LaTeX sources of all three documents are in [`docs/src/`](docs/src/).

## How this was made

Everything in this repository was produced by AI models: Claude Opus 5.5 in Claude Code (entropy proof, both Lean formalizations, literature search), gpt-6-astra in Codex (compression proof, the rewrite, the fact-check of the related-work section), and Claude Fable 5.1 (review of the compression proof). The question came from a friend of the repository owner, who had the n log n lower bound from {1, …, n} and conjectured that it was tight. Both models independently showed that it is not, by finding the extra log log n factor: Codex in about 23 minutes, Claude in about an hour, including a first attempt lost to a connection error. [`docs/how-it-was-made.md`](docs/how-it-was-made.md) records which model produced each artifact, with settings, timings, token counts, tools and outside sources, and compares the two approaches.

## Statement

```lean
/-- The least positive integer `k` with `k * a ∉ S`. -/
noncomputable def kVal (S : Finset ℕ) (a : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ k * a ∉ S}

theorem main_theorem :
    (∃ C : ℝ, ∃ N : ℕ, ∀ S : Finset ℕ, (∀ a ∈ S, 0 < a) → N ≤ S.card →
      ((∑ a ∈ S, kVal S a : ℕ) : ℝ) ≤ C * S.card * Real.log S.card * Real.log (Real.log S.card)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ S : Finset ℕ, (∀ a ∈ S, 0 < a) ∧
      S.card = n ∧ c * n * Real.log n * Real.log (Real.log n) ≤ ((∑ a ∈ S, kVal S a : ℕ) : ℝ))
```

`main_theorem_alt` has the identical statement. `RunsOfMultiplesLean/Examples.lean` checks the definition on small cases, for example `Σ k = 16` for `{1, 2, 3, 4, 6}` against `15` for `{1, …, 5}`.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.35.0-rc4`, with the matching Mathlib release).

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```

With the Mathlib cache in place, building this project takes one to a few minutes. The files use narrow Mathlib imports rather than `import Mathlib`, which keeps compile time and memory use low. Lake prints notes suggesting the new Lean module system for files importing Mathlib; they are informational.

## Proof 1: entropy (`RunsOfMultiplesLean/`)

Lemma and equation numbers refer to [`docs/runs-of-multiples.pdf`](docs/runs-of-multiples.pdf).

| File | Content |
|---|---|
| `Defs.lean` | `kVal`, the runs `A S t`, `L = kVal − 1`, `Σ kVal = n + Σ L` |
| `Entropy.lean` | counting entropy `ent`, the smooth part `key t m`, the conditional entropies `D T t`, chain rule `sum_D` (identity (2)) |
| `OneStep.lean` | Lemma 3 `ent_ge_of_shift` and corollaries `ent_ge_log_two`, `ent_ge_sparse` |
| `Edges.lean` | Lemma 4 `edge_bound` and its consequence (3) |
| `Upper.lean` | the main argument: `fibre_bound` (all four classes in one per-fibre inequality), `prime_bound`, `double_count`, `upper_core`, `upper_of_primeInput` (prime-counting facts as the hypothesis `PrimeInput`) |
| `Primes.lean` | `PrimeInput` from Mathlib's Chebyshev bounds: `θ(m) ≥ (log 2/2) m − C` and at least `q^(3/4)` primes in `(q, 4q]`; `upper_bound` |
| `Lower.lean` | smooth numbers `Sm X y`, Rankin's estimate via Mathlib's Euler product, a pigeonhole over `X = y^i`, replication to every `n`; `lower_bound` |
| `Main.lean` | `main_theorem` |

Differences from the write-up: primes in `(q, 4q]` replace `(q, 2q]`, so Chebyshev's bounds suffice and the prime number theorem is not needed; the cutoff is `(log n)^8` instead of `(log n)^4`; the lower bound pads with scaled copies `M^j · S_y` and extra integers instead of prime dilates.

## Proof 2: compression (`RunsOfMultiplesLean/Alt/`)

Lemma and equation numbers refer to [`docs/first-missing-multiple.pdf`](docs/first-missing-multiple.pdf).

| File | Content |
|---|---|
| `Alt/Defs.lean` | the closure properties `DivClosed` (i) and `ShiftClosed` (ii) |
| `Alt/Compression.lean` | abstract chain systems: Lemma 1 (`card_A_le_comp`), cardinality (`card_comp`), sum decrease (`sum_comp_le`) |
| `Alt/Chains.lean` | the two compressions `pChain p` and `pqChain p q` with their window conditions; Lemma 2 `exists_closed` |
| `Alt/Radical.lean` | Lemma 3 (`radical_bound`), equation (7) (`sum_theta_L_le`), `sum_L_le_of_closed` |
| `Alt/Upper.lean` | `upper_bound_alt` |
| `Alt/Lower.lean` | the set `Sy` and its exact size `(H+1)^q · C(2m, m)` (`card_Sy`), good elements, `card_Sy_le` (at least a quarter good), size bound; `lower_bound_alt` |
| `Alt/Main.lean` | `main_theorem_alt` |

Differences from the write-up: Lemma 2 takes a compression-stable set of minimal element sum instead of iterating the compressions until nothing changes; Lemma 3 bounds each fibre by `m^m` instead of `m!`; `log p ≤ (4/3) log π(p) + O(1)` comes from the prime-gap estimate in `Primes.lean`; equation (7) is used as an inequality; the size bound uses `H + 1 ≤ y^4`; the padding step reuses `replicate` from `Lower.lean`.

The two proofs share `Defs.lean`, the Chebyshev inputs in `Primes.lean` and the padding lemma `replicate`.

## Status and related work

We are not aware of an earlier determination of this extremal quantity. Our searches of the Erdős problems database, MathOverflow and Math.SE, olympiad collections, arXiv and the OEIS found no statement of the problem or its answer. We did not consult MathSciNet, zbMATH Open, Guy's *Unsolved Problems in Number Theory* or Hall's *Sets of Multiples*. Pointers to earlier appearances are welcome as issues.

**Earlier appearance of the quantity.** Σ k(a) governs the worst-case number of membership checks in the standard solution to Codeforces problem [1732D1 "Balance (Easy version)"](https://codeforces.com/problemset/problem/1732/D1) (October 2022). Starting from the set {0}, the problem receives insertions, and a query asks for the smallest non-negative multiple of k that is not in the set; the solution caches each k's previous answer and resumes scanning there. The [editorial](https://codeforces.com/blog/entry/108327) argues informally that the solution "will work quite quickly". An informal analysis in [blog entry 108425](https://codeforces.com/blog/entry/108425) proposes S = {1, …, q/2} as the worst case and derives O(q log q) membership checks. The theorem shows that the worst case is Θ(q log q log log q) membership checks. The difference is visible at contest scale: the first 10⁵ 53-smooth numbers need 1,443,333 membership checks, against 1,266,750 for {1, …, 10⁵}, with every element below 7.4 · 10⁶.

**A product-set corollary** (not formalized here). Applying the theorem to S = A · {1, …, t} gives |A · {1, …, t}| ≥ c |A| t / (log N log log N) with N = |A · {1, …, t}|, for every finite set A of positive integers, and smooth numbers show that this is sharp. For each fixed C, the case t ≤ (log N)^C, with a constant depending on C, follows from the Plünnecke–Ruzsa inequality and elementary prime counting; we found no statement of the version uniform in t. Bounds of this kind are known for special sets A, for example Ford's theorem on the multiplication table ([Annals of Mathematics 168, 2008](https://annals.math.princeton.edu/2008/168-2/p01)), Koukoulopoulos's generalized multiplication tables ([J. Reine Angew. Math. 689, 2014; arXiv:1102.3236](https://arxiv.org/abs/1102.3236)) and Xu and Zhou on products of arithmetic progressions ([Discrete Analysis 2023:10; arXiv:2201.00104](https://arxiv.org/abs/2201.00104)).

**Closest related work.**

- Extremal problems analyzed through smooth numbers: [Erdős problem #168](https://www.erdosproblems.com/168) asks for the limiting maximum density of subsets of {1, …, N} avoiding {n, 2n, 3n}. Graham, Witsenhausen and Spencer (1977) proved that the limit exists and expressed it through an extremal problem on 3-smooth numbers.
- Reciprocal sums of primitive sets: refining earlier work of Behrend, Pillai and Erdős, Erdős, Sárközy and Szemerédi ([J. London Math. Soc. 42, 1967](https://www.renyi.hu/~p_erdos/1967-10.pdf)) determined the asymptotic maximum of Σ_{a∈A} 1/a over sets A ⊆ {1, …, n} in which no element divides another; the answer involves log log n.
- Entropy and prime factorisations: Kontoyiannis ([arXiv:0710.4076](https://arxiv.org/abs/0710.4076), 2007) gives an information-theoretic proof of Σ_{p≤n} (log p)/p ∼ log n, and Tao ([Smooth numbers and max-entropy, 2025](https://terrytao.wordpress.com/2025/09/15/smooth-numbers-and-max-entropy/)) develops a maximum-entropy heuristic for the distribution of smooth numbers.
- Edge counts and compression in grids: Han's entropy inequality (1978), the Clements–Lindström shadow theorem for products of chains (1969), and the edge-isoperimetric inequalities in grids of [Bollobás and Leader (Combinatorica 11, 1991)](https://digitalcommons.memphis.edu/facpubs/4558/) and [Ahlswede and Bezrukov (Appl. Math. Lett. 8, 1995)](https://www.math.uni-bielefeld.de/ahlswede/homepage/public/99.pdf). The unweighted edge count in the first proof (Lemma 4 of `docs/runs-of-multiples.pdf`) can also be obtained from Han's inequality by the classical argument for edges in the hypercube. We are not aware of earlier versions of the specific prime-weighted entropy inequality used there (Lemma 3 and its use in Section 3.2), or of the compression in the second proof that replaces a prime factor by a smaller prime.

## License

Apache License 2.0, see [`LICENSE`](LICENSE).
