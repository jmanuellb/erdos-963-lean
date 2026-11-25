module

public import E963.Main

/-!
# Erdős Problem 963, part i: the proved statement

This module declares the theorem of `Challenge.lean` with a complete proof. The definition of `f`
is in `E963/Defs.lean` and is identical to the one in `Challenge.lean`. The proof is
`Erdos963.f_isEquivalent_logb` in `E963/Main.lean`. See `docs/PROOF.md` for the mathematics.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos963

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
    (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] erdos_963.parts.i.answer :=
  f_isEquivalent_logb

end Erdos963
