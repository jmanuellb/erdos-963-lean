# Erdős Problem 963, part i, in Lean 4

A complete, `sorry`-free Lean 4 / Mathlib formalization of part i of
[Erdős Problem 963](https://www.erdosproblems.com/963): the largest guaranteed size `f(n)` of a
dissociated subset of an `n`-element set of reals satisfies `f(n) ~ log₂ n`.

## The problem

A finite set `B ⊂ ℝ` is *dissociated* if its `2^|B|` subset sums are pairwise distinct. Let `f(n)`
be the largest `k` such that every `n`-element set `A ⊂ ℝ` contains a dissociated subset of size
at least `k`. Erdős asked to estimate `f(n)`; part i asks for the asymptotics, part ii whether
`f(n) ≥ ⌊log₂ n⌋` for all `n`.

This repository proves part i with answer `log₂ n`. **Part ii is not addressed.**

## Lean statement

Definitions (`E963/Defs.lean`, copied from the formal-conjectures statement, see Attribution):

```lean
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)}
```

Main theorem (`E963/Main.lean`, namespace `Erdos963`):

```lean
noncomputable def erdos_963.parts.i.answer : ℕ → ℝ := fun n ↦ Real.logb 2 n

theorem erdos_963.parts.i :
    (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] erdos_963.parts.i.answer
```

Fully qualified name: `Erdos963.erdos_963.parts.i`. The statement is the one of
`FormalConjectures/ErdosProblems/963.lean` (where `answer` is left as `sorry`) with the answer
`n ↦ log₂ n` filled in.

Explicit bounds proved along the way:

* `Erdos963.f_upper : f n ≤ Nat.log 2 (Nat.log 2 (n * n + 1) * n + 1)`
* `Erdos963.f_lower : 1 ≤ m → (4*m*J^5 + 1) * J^t ≤ n → t * m ≤ f n`, with `J = 2^(m+4) * (m + t*m)`

## Proof outline

The full write-up is in [`docs/PROOF.md`](docs/PROOF.md); the Lean files follow it lemma by lemma,
with the same constants.

1. **Upper bound.** In `{1, …, n}` a dissociated subset of size `k` has `2^k` distinct subset sums
   in `[0, kn]`, so `2^k ≤ kn + 1`, giving `f(n) ≤ log₂ n + O(log log n)`.
2. **Reduction to integers.** A `ℚ`-linear functional separating the finitely many differences maps
   any finite `A ⊂ ℝ` injectively into `ℤ`, reflecting dissociativity.
3. **Fejér kernel.** Work modulo a large prime `q` with `K_M = |Σ_{j≤M} e(jx)|²`. Orthogonality of
   additive characters (Parseval) gives a second-moment bound over dilations `r`, so for most `r`
   some element of `rA` lies near each target `2^j g`.
4. **Dirichlet.** For every `x` some `s ≤ J` makes `s·x` small mod `q`; by pigeonhole one `s` works
   for a `1/J` fraction of `A`.
5. **Lifting lemma.** Elements near `2^j g` (binary "digits") can be added to any small dissociated
   set of elements near `0`, keeping it dissociated (uniqueness of binary expansions).
6. **Step and iteration.** Each step gains `m` elements while dividing the size of the set by
   `J ≈ 2^m · poly(m)`; iterating `t` times gives `f(n) ≥ (t/(t+7)) log₂ n − O_t(1)` for each `t`.
7. Combining with 1 yields `f(n) ~ log₂ n`.

## Files

| File | Content |
| --- | --- |
| `E963/Defs.lean` | `f`, `le_f`, `f_le` (from formal-conjectures) |
| `E963/Kernel.lean` | Fejér kernel decay, Parseval, second moment |
| `E963/Step.lean` | bad multipliers, hits, Dirichlet, lifting lemma |
| `E963/StepThm.lean` | the step theorem |
| `E963/Iterate.lean` | iteration, reduction to integers, `f_lower` |
| `E963/Upper.lean` | `f_upper` |
| `E963/Main.lean` | asymptotic lower bound and `erdos_963.parts.i` |
| `E963/Axioms.lean` | axiom audit |
| `docs/PROOF.md` | the mathematical proof |

## Versions

* Lean `v4.36.0` (`lean-toolchain`: `leanprover/lean4:v4.36.0`)
* Mathlib `v4.36.0`, pinned to commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
  (`lakefile.toml` and `lake-manifest.json`)

## Reproduction

```bash
# with elan installed
lake exe cache get     # download prebuilt Mathlib oleans
lake build             # builds the E963 library, including E963/Axioms.lean
```

On a heavily loaded Windows machine, building several modules that import `Mathlib` in parallel
occasionally failed with a spurious `failed to read file '…/Mathlib/….olean.private'`. Building
the modules one at a time (`lake build E963.<Module>`, then `lake build`) worked.

## Axiom audit

`lake build` compiles `E963/Axioms.lean`, which prints (excerpt; it also echoes the statement and definitions):

```
info: E963/Axioms.lean:5:0: 'Erdos963.erdos_963.parts.i' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E963/Axioms.lean:6:0: 'Erdos963.f_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
info: E963/Axioms.lean:7:0: 'Erdos963.f_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard axioms of Lean/Mathlib are used. The sources contain no `sorry`, `admit`,
`axiom` or `native_decide`.

## Attribution

* **Mathematics.** The strategy of the lower bound (random dilation modulo a prime, then a
  recursion that gains about `m` elements while dividing the size of the set by about `2^m`) is due
  to the user **KoishiChan**, in a comment in the erdosproblems.com forum thread for problem 963
  (December 2025). The mathematical credit for the idea is theirs. The write-up in `docs/PROOF.md`
  is an elementary variant of that argument (Fejér-kernel second moment instead of a fourth-moment
  estimate, Dirichlet's pigeonhole instead of a second moment for the elements near 0). This
  repository covers **only part i** of the problem.
* **Statement.** The definition of `f` and the statement `erdos_963.parts.i` are taken from
  `FormalConjectures/ErdosProblems/963.lean` in
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (Apache License 2.0); only the `@[category …]` attributes were dropped and the `answer` filled in.
* **Formalization:** `<AUTHOR>`.

## License

Apache License 2.0, see [`LICENSE`](LICENSE).
