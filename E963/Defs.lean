import Mathlib

/-!
# Erdős Problem 963 — definitions

The definition of `f` and the two API lemmas are copied verbatim from
`FormalConjectures/ErdosProblems/963.lean` (google-deepmind/formal-conjectures); only the
attributes `@[category ...]` (which need `FormalConjecturesUtil`) are dropped.
-/

open Filter Asymptotics

namespace Erdos963

/-- $f(n)$ is the largest $k$ such that every set $A\subset\mathbb{R}$ with $n$ elements has a
dissociated subset with at least $k$ elements. The set of such $k$ contains $0$ (take the empty
subset) and is bounded by $n$, so `sSup` is a true maximum. The set $A$ may contain $0$, which
can never belong to a dissociated set. For $n = 0$ the value is $0$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)}

/-- If every set of `n` reals has a dissociated subset with at least `k` elements, then
$k \leq f(n)$. -/
theorem le_f {n k : ℕ}
    (h : ∀ A : Finset ℝ, A.card = n → ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)) :
    k ≤ f n := by
  refine le_csSup ⟨n, fun m hm ↦ ?_⟩ h
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq ℝ n
  obtain ⟨B, hBA, hmB, -⟩ := hm A hA
  exact hmB.trans ((Finset.card_le_card hBA).trans hA.le)

/-- If `A` has `n` elements and all dissociated subsets of `A` have at most `m` elements, then
$f(n) \leq m$. -/
theorem f_le {n m : ℕ} (A : Finset ℝ) (hA : A.card = n)
    (h : ∀ B ⊆ A, AddDissociated (B : Set ℝ) → B.card ≤ m) : f n ≤ m := by
  refine csSup_le ⟨0, fun A' _ ↦ ⟨∅, Finset.empty_subset _, Nat.zero_le _, by simp⟩⟩ ?_
  intro k hk
  obtain ⟨B, hBA, hkB, hB⟩ := hk A hA
  exact hkB.trans (h B hBA hB)

end Erdos963
