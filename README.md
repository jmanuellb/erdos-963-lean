# Erdős Problem 963, part i, in Lean 4

A Lean 4 / Mathlib proof of the first part of
[Erdős Problem 963](https://www.erdosproblems.com/963): the largest guaranteed size `f(n)` of a
dissociated subset of an `n`-element set of real numbers satisfies `f(n) ~ log₂ n`.

**Scope.** Only part i is proved. Part ii of the problem, whether `f(n) ≥ ⌊log₂ n⌋` for every
`n`, is open and is not addressed here. The problem as a whole is not solved by this repository.

## The problem

A finite set `B ⊂ ℝ` is *dissociated* if its `2^|B|` subset sums are pairwise distinct. Let `f(n)`
be the largest `k` such that every `n`-element set `A ⊂ ℝ` contains a dissociated subset of size
at least `k`. Erdős [Er65, p. 188] asked to estimate `f(n)`, and in particular whether
`f(n) ≥ ⌊log₂ n⌋`. He noted that the greedy algorithm gives `f(n) ≥ ⌊log₃ n⌋`.

* Part i: estimate `f(n)`. Read as an asymptotic equivalence, the answer is `f(n) ~ log₂ n`.
  **Proved here.**
* Part ii: is `f(n) ≥ ⌊log₂ n⌋` for all `n`? **Open. Not addressed here.** Part i does not imply
  it: `f(n) ≥ (1 − o(1)) log₂ n` says nothing for a fixed `n`.

## Lean statement

The statement is the one of `FormalConjectures/ErdosProblems/963.lean` in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
where the value of `answer` is left open. It is in [`Challenge.lean`](Challenge.lean):

```lean
namespace Erdos963

noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)}

noncomputable def erdos_963.parts.i.answer : ℕ → ℝ := fun n ↦ Real.logb 2 n

theorem erdos_963.parts.i :
    (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] erdos_963.parts.i.answer
```

`AddDissociated` is Mathlib's definition. `~[atTop]` is `Asymptotics.IsEquivalent`:
`f(n) − log₂ n = o(log₂ n)` as `n → ∞`. The set `A` may contain `0` and negative numbers.

Explicit bounds proved along the way (`E963/Upper.lean`, `E963/Iterate.lean`):

* `Erdos963.f_upper : f n ≤ Nat.log 2 (Nat.log 2 (n * n + 1) * n + 1)`
* `Erdos963.f_lower : 1 ≤ m → (4*m*J^5 + 1) * J^t ≤ n → t * m ≤ f n`, with `J = 2^(m+4) * (m + t*m)`

## Layout

The repository follows the Challenge/Solution layout of `lake comparator`, which the
[Palomar registry](https://palomar-registry.org/) requires.

| File | Content |
| --- | --- |
| `Challenge.lean` | the statement only (`f`, `answer`, the theorem with `sorry`); imports only Mathlib |
| `Solution.lean` | the same theorem with its proof |
| `comparator.json` | tells `lake comparator` to compare `Erdos963.erdos_963.parts.i` |
| `formalization.yaml` | provenance, sources, scope and AI disclosure |
| `E963/Defs.lean` | `f`, `le_f`, `f_le` (from formal-conjectures) |
| `E963/Kernel.lean` | Fejér-type kernel decay, Parseval, second moment |
| `E963/Step.lean` | bad multipliers, hits, Dirichlet, lifting lemma |
| `E963/StepThm.lean` | the step theorem |
| `E963/Iterate.lean` | iteration, reduction to integers, `f_lower` |
| `E963/Upper.lean` | `f_upper` |
| `E963/Main.lean` | asymptotic bounds and `f_isEquivalent_logb` |
| `E963/Axioms.lean` | axiom audit |
| `docs/PROOF.md` | the mathematical proof |

`Challenge.lean` contains one deliberate `sorry`: it is the statement to be compared, not a
proof. No other file contains `sorry`, `admit`, `axiom` or `native_decide`.

## Proof outline

The full write-up is in [`docs/PROOF.md`](docs/PROOF.md). The Lean files follow it lemma by lemma,
with the same constants.

1. **Upper bound.** In `{1, …, n}` a dissociated subset of size `k` has `2^k` distinct subset sums
   in `[0, kn]`, so `2^k ≤ kn + 1`, giving `f(n) ≤ log₂ n + O(log log n)`.
2. **Reduction to integers.** A `ℚ`-linear functional separating the finitely many differences maps
   any finite `A ⊂ ℝ` injectively into `ℤ`, reflecting dissociativity.
3. **Fejér-type kernel.** Work modulo a large prime `q` with `K_M = |Σ_{j≤M} e(jx)|²`.
   Orthogonality of additive characters (Parseval) gives a second-moment bound over dilations `r`,
   so for most `r` some element of `rA` lies near each target `2^j g`.
4. **Dirichlet.** For every `x` some `s ≤ J` makes `s·x` small mod `q`. By pigeonhole one `s` works
   for a `1/J` fraction of `A`.
5. **Lifting lemma.** Elements near `2^j g` (binary "digits") can be added to any small dissociated
   set of elements near `0`, keeping it dissociated (uniqueness of binary expansions).
6. **Step and iteration.** Each step gains `m` elements while dividing the size of the set by
   `J ≈ 2^m · poly(m)`. Iterating `t` times gives `f(n) ≥ (t/(t+7)) log₂ n − O_t(1)` for each `t`.
7. Combining with 1 yields `f(n) ~ log₂ n`.

## Attribution

* **The lower bound is not ours.** The bound `f(n) ≥ (1 − o(1)) log₂ n` and the strategy of its
  proof (reduce to integers, multiply by a random residue modulo a large prime, then a recursion
  that gains about `m` elements while dividing the size of the set by about `2^m`) are due to the
  user **KoishiChan**, in a
  [comment of 5 December 2025](https://www.erdosproblems.com/forum/thread/963#post-2027) in the
  erdosproblems.com forum thread for Problem 963. Quanyu Tang, Terence Tao and Thomas Bloom
  commented on the argument in the same thread. The mathematical credit for the result belongs to
  KoishiChan. We have not contacted them.
* **What differs.** `docs/PROOF.md` is a variant of that argument made elementary for
  formalization. The forum argument uses a second moment over Dirichlet characters, the
  Montgomery–Vaughan fourth-moment estimate for character sums, and an intermediate modulus `p`.
  Here these are replaced by a second moment for a Fejér-type kernel (only orthogonality of
  additive characters), Dirichlet's pigeonhole principle for the elements near `0`, and the
  residues `2^j g` as targets. We do not claim that this variant is new mathematics of
  independent interest. No human expert has reviewed `docs/PROOF.md`.
* **The upper bound** is the counting argument for Erdős's example `a_i = i` [Er65, p. 188].
* **Statement.** The definition of `f` and the statement `erdos_963.parts.i` are taken from
  `FormalConjectures/ErdosProblems/963.lean` in
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (Apache License 2.0, Copyright 2026 The Formal Conjectures Authors). The `@[category …]`
  attributes were dropped and the `answer` was filled in.
* **Formalization:** `<AUTHOR>`.

## AI assistance

The informal proof in `docs/PROOF.md` and the Lean development were written with AI assistance
(Anthropic's Claude models, run as coding agents with Claude Code), directed by the author. The
proof is checked by the Lean kernel. A separate agent session audited the result: clean rebuild,
`leanchecker` replay, axiom listing, and a comparison of the statement with formal-conjectures.
No human mathematician has refereed the informal proof.

## Versions

* Lean `v4.36.0` (`lean-toolchain`: `leanprover/lean4:v4.36.0`)
* Mathlib `v4.36.0`, pinned to commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
  (`lakefile.toml` and `lake-manifest.json`)
* All `.lean` files use Lean's module system.

## How to build

```bash
# with elan installed
lake exe cache get     # download prebuilt Mathlib oleans
lake build             # builds E963, Challenge and Solution
```

`lake build` ends with `Build completed successfully`. It prints the warning
``declaration uses `sorry` `` for `Challenge.lean`, which is the deliberate statement stub, and
Mathlib style-linter warnings about file headers. `Solution.lean` and `E963/` build without any
warning about `sorry`.

On a heavily loaded Windows machine, building several modules that import `Mathlib` in parallel
occasionally failed with a spurious `failed to read file '…/Mathlib/….olean.private'`. Building
the modules one at a time (`lake build E963.<Module>`, then `lake build`) worked.

## Axiom audit

`lake build` compiles `E963/Axioms.lean`, which prints:

```
info: E963/Axioms.lean:12:0: 'Erdos963.erdos_963.parts.i' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E963/Axioms.lean:13:0: 'Erdos963.f_isEquivalent_logb' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E963/Axioms.lean:14:0: 'Erdos963.f_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E963/Axioms.lean:15:0: 'Erdos963.f_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard axioms of Lean and Mathlib are used.

## Comparator and Palomar

`lake comparator` checks that the theorem in `Solution.lean` has the same statement as the one in
`Challenge.lean`, including the definitions it depends on, and uses only the permitted axioms. It
needs Linux with `bwrap`:

```bash
lake exe cache get
lake comparator --config comparator.json
```

This check was **not** run on the machine where the proof was developed (Windows, where
`lake comparator` refuses to start). As a partial substitute, the raw terms of `f`, of `answer`
and of the type of the theorem were printed once from `Challenge` and once from `Solution`, and
were identical. The CI workflow in `.github/workflows/ci.yml` runs the real check on Linux
(`scripts/verify-comparator.sh`, from PalomarTemplate). It has not been run yet. Palomar runs its
own verification when the repository is submitted at
[submit.palomar-registry.org](https://submit.palomar-registry.org/).

## References

* [Er65] P. Erdős, *Extremal problems in number theory*. Proc. Sympos. Pure Math., Vol. VIII
  (1965), 181–189. [PDF](https://www.renyi.hu/~p_erdos/1965-02.pdf)
* T. F. Bloom, *Erdős Problem #963*, <https://www.erdosproblems.com/963>.
* KoishiChan, comment in the forum thread for Problem 963, 5 December 2025,
  <https://www.erdosproblems.com/forum/thread/963#post-2027>.

## License

Apache License 2.0, see [`LICENSE`](LICENSE).
