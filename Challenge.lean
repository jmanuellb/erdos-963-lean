module

public import Mathlib

/-!
# Erdős Problem 963, part i: the statement

*References:*
- [erdosproblems.com/963](https://www.erdosproblems.com/963)
- [Er65] Erdős, P., *Extremal problems in number theory*. Proc. Sympos. Pure Math., Vol. VIII
  (1965), 181-189.

A finite set `B` of real numbers is dissociated if the sums over its subsets are pairwise
distinct. This is `AddDissociated` in Mathlib. Let $f(n)$ be the largest $k$ such that every set
of $n$ real numbers has a dissociated subset with at least $k$ elements. Erdős asked to estimate
$f(n)$, and in particular whether $f(n)\geq\lfloor\log_2 n\rfloor$.

This file states the first part, read as an asymptotic equivalence: $f(n)\sim\log_2 n$. It does
not state the second part, $f(n)\geq\lfloor\log_2 n\rfloor$ for all $n$, which is open.

The definition of `f` and the statement `erdos_963.parts.i` are those of
`FormalConjectures/ErdosProblems/963.lean` in google-deepmind/formal-conjectures (Apache-2.0).
There the value of `erdos_963.parts.i.answer` is left open. Here it is `fun n ↦ Real.logb 2 n`.

The only declaration with `sorry` is the theorem. Its proof is in `Solution.lean`.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos963

/-- $f(n)$ is the largest $k$ such that every set $A\subset\mathbb{R}$ with $n$ elements has a
dissociated subset with at least $k$ elements. The set of such $k$ contains $0$ (take the empty
subset) and is bounded by $n$, so `sSup` is a true maximum. The set $A$ may contain $0$, which
can never belong to a dissociated set. For $n = 0$ the value is $0$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)}

/-- The answer to part i: $f(n)\sim\log_2 n$. For $n = 0$ the value `Real.logb 2 0` is $0$. This
does not matter for the asymptotic statement. -/
noncomputable def erdos_963.parts.i.answer : ℕ → ℝ := fun n ↦ Real.logb 2 n

/--
Let $f(n)$ be the maximal $k$ such that in any set $A\subset \mathbb{R}$ of size $n$ there is a
subset $B\subseteq A$ of size $\lvert B\rvert\geq k$ which is dissociated, that is, the sums
$\sum_{b\in S}b$ are distinct for all $S\subseteq B$. Estimate $f(n)$.

This is the first part of Erdős problem 963, read as an asymptotic equivalence
$f(n)\sim$ `answer n`, that is, $f(n)-\log_2 n=o(\log_2 n)$ as $n\to\infty$
(`Asymptotics.IsEquivalent` along `Filter.atTop`). The answer is $\log_2 n$.
-/
theorem erdos_963.parts.i :
    (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] erdos_963.parts.i.answer := by
  sorry

end Erdos963
