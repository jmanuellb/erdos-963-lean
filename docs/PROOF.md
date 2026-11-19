# Erdős problem 963, part i: f(n) = (1 + o(1)) log₂ n

Self-contained proof. The strategy (random dilation modulo a prime, then a recursion that
gains about m elements while dividing the size of the set by about 2^m) is the one sketched by
"KoishiChan" in the erdosproblems.com forum thread of problem 963 (December 2025). The
mathematical credit for the idea is theirs. The write-up below is ours and differs in three
ways, all chosen so that the proof is elementary and formalizable:

* the Montgomery–Vaughan fourth-moment estimate is replaced by a Fejér-kernel second moment
  that needs only orthogonality of additive characters (Lemmas 2–4);
* the "many elements near 0" part is obtained deterministically by Dirichlet's pigeonhole
  principle instead of a second moment (Lemma 5);
* there is no intermediate modulus p: the targets are the residues 2^j·g directly.

The Lean 4 formalization (`E963/`) follows this text lemma by lemma, with the same
constants.

## 0. Statement

A finite set B of reals is *dissociated* if the 2^|B| subset sums are pairwise distinct;
equivalently, there are no two different (or: disjoint and different) subsets with the same sum.
f(n) is the largest k such that every n-element set of reals has a dissociated subset of
size ≥ k.

**Theorem.** f(n) ~ log₂ n, i.e. f(n)/log₂ n → 1.

More precisely:

* (upper) f(n) ≤ log₂( n·⌊log₂(n²+1)⌋ + 1 ) ≤ log₂ n + log₂(2 log₂ n + 2) for n ≥ 1;
* (lower) for every t ≥ 1 there is m₀(t) such that f(n) ≥ t·m whenever m ≥ m₀(t) and
  n ≥ 2^{m(t+7)}; hence f(n) ≥ (t/(t+7))·log₂ n − O_t(1).

## 1. Upper bound

Take A = {1, …, n}. Let B ⊆ A be dissociated, k = |B|. The 2^k subset sums are distinct
integers in [0, kn], so 2^k ≤ kn + 1. Since k ≤ n this gives 2^k ≤ n² + 1, so
k ≤ L := ⌊log₂(n²+1)⌋, and then 2^k ≤ Ln + 1, so k ≤ ⌊log₂(Ln+1)⌋. Hence
f(n) ≤ log₂(Ln + 1) ≤ log₂((L+1)n) = log₂ n + log₂(L+1), and
L ≤ log₂(2n²) = 1 + 2 log₂ n. Since log₂(2+2x) = o(x), f(n) − log₂ n ≤ o(log₂ n).

## 2. Reduction to integers

**Lemma 1.** For every finite A ⊂ ℝ there is a map φ : ℝ → ℤ, injective on A, such that for
every B ⊆ A: if φ(B) is dissociated then B is dissociated.

*Proof.* ℝ is a vector space over the infinite field ℚ. The finitely many nonzero differences
a − a′ (a, a′ ∈ A) are nonzero vectors, and a vector space over an infinite field is not a
finite union of proper subspaces (applied to the dual: the kernels of the evaluations at these
vectors); so there is a ℚ-linear g : ℝ → ℚ with g(a − a′) ≠ 0 for all a ≠ a′ in A. Let N be
the product of the denominators of g(a), a ∈ A, and φ(x) = ⌊N·g(x)⌋, so φ(a) = N·g(a) for
a ∈ A. φ is injective on A. If t, u ⊆ B have equal sums then, by linearity of g,
Σ_{x∈t} φ(x) = N·g(Σ_t x) = Σ_{x∈u} φ(x); by injectivity these are the sums of the sets
φ(t), φ(u) ⊆ φ(B), so φ(t) = φ(u) and t = u. ∎

So it suffices to find large dissociated subsets in finite sets of integers.

## 3. Characters and the Fejér kernel

Let q be a prime, e(x) = exp(2πi x/q) for x ∈ ℤ/q, and |x| the absolute value of the
representative of x in (−q/2, q/2]. For M ≥ 0 put

  D_M(x) = Σ_{j=0}^{M} e(jx),  K_M(x) = |D_M(x)|² ≥ 0.

**Lemma 2 (decay).** For x ≠ 0: K_M(x) ≤ q² / (4|x|²).

*Proof.* D_M(x)(e(x) − 1) = e((M+1)x) − 1, so |D_M(x)| ≤ 2/|e(x) − 1|. With v the centered
representative of x, |e(x) − 1| = 2|sin(πv/q)| ≥ 2·(2/π)·π|v|/q = 4|v|/q because |πv/q| ≤ π/2
and sin y ≥ 2y/π on [0, π/2]. ∎

For a set A ⊆ ℤ/q, a center c and a multiplier r, define

  S_A(η) = Σ_{a∈A} e(ηa),  N_c(r) = Σ_{a∈A} K_M(ra − c).

**Lemma 3 (Parseval).** Σ_{η∈ℤ/q} |S_A(η)|² = q|A|.

*Proof.* |S_A(η)|² = Σ_{a,b∈A} e(η(a−b)) and Σ_η e(ηz) = q·1[z = 0]. ∎

**Lemma 4 (second moment).** If M + 1 ≤ q then

  Σ_{r∈ℤ/q} ( N_c(r) − |A|(M+1) )² ≤ (M+1)⁴ · q · |A|.

*Proof.* K_M(y) = Σ_{0≤j,j′≤M} e((j−j′)y). The diagonal terms contribute exactly M+1, hence

  N_c(r) − |A|(M+1) = Σ_{j≠j′} e(−(j−j′)c) · S_A((j−j′)r).

There are at most (M+1)² pairs, so by the triangle and Cauchy–Schwarz inequalities

  (N_c(r) − |A|(M+1))² ≤ (M+1)² Σ_{j≠j′} |S_A((j−j′)r)|².

For j ≠ j′ in [0, M] and M < q the residue j − j′ is invertible, so r ↦ (j−j′)r is a
bijection of ℤ/q and Σ_r |S_A((j−j′)r)|² = q|A| by Lemma 3. Summing over the ≤ (M+1)²
pairs gives the claim. ∎

**Corollary A (few bad multipliers).** The number of r ∈ ℤ/q with N_c(r) ≤ |A|(M+1)/2 is at
most 4(M+1)² q / |A|.

*Proof.* Each such r contributes at least (|A|(M+1)/2)² to the sum in Lemma 4. ∎

**Corollary B (a hit).** If N_c(r) > |A|(M+1)/2 then there are a ∈ A and an integer v ≡ ra − c
(mod q) with 2(M+1)v² < q².

*Proof.* Otherwise every a ∈ A has ra − c ≠ 0 and, with v its centered representative,
q² ≤ 2(M+1)v², so K_M(ra − c) ≤ q²/(4v²) ≤ (M+1)/2 by Lemma 2; summing, N_c(r) ≤ |A|(M+1)/2. ∎

## 4. Dirichlet

**Lemma 5.** Let w, J ≥ 1 with q ≤ wJ and x ∈ ℤ/q. There are 1 ≤ s ≤ J and an integer v ≡ sx
(mod q) with |v| < w.

*Proof.* The J + 1 residues tx (0 ≤ t ≤ J), written in [0, q), fall into the J classes
⌊·/w⌋ ∈ [0, J). Two of them, t < t′, fall in the same class; s = t′ − t and v the difference of
the two representatives work. ∎

## 5. The lifting lemma

**Lemma 6.** Let q ≥ 1, r ∈ ℤ/q, and let g, ρ, m, K be natural numbers with

  (m + K)·ρ < g and g·2^{m+1} ≤ q.

For an integer x let ν(x) ∈ (−q/2, q/2] be the centered representative of r·x. Let
a_0, …, a_{m−1} be integers with |ν(a_j) − 2^j g| ≤ ρ, and let D be a dissociated set of
integers with |D| ≤ K and |ν(d)| ≤ ρ for all d ∈ D. Then the a_j are pairwise distinct, none
of them lies in D, and D ∪ {a_0, …, a_{m−1}} is dissociated.

*Proof.* If j < j′ then 2^{j′}g − 2^j g ≥ g > 2ρ (here m ≥ 2), so ν(a_j) ≠ ν(a_{j′}).
If a_j ∈ D then 2^j g ≤ 2ρ < g (here m, K ≥ 1), impossible.

Suppose t, u ⊆ D ∪ E (E = {a_j}) are disjoint, different, and have the same sum. For x ∈ D ∪ E
put β(x) = 2^j if x = a_j and β(x) = 0 if x ∈ D, and e(x) = ν(x) − g·β(x), so |e(x)| ≤ ρ.
Since Σ_t x = Σ_u x, multiplying by r gives Σ_t ν(x) ≡ Σ_u ν(x) (mod q). Now

  Σ_t ν − Σ_u ν = g·Z + W,  Z = Σ_t β − Σ_u β,  W = Σ_t e − Σ_u e.

Both Σ_t β and Σ_u β are sums of distinct powers 2^j with j < m, so they lie in [0, 2^m − 1]
and |Z| ≤ 2^m − 1. As t and u are disjoint, |W| ≤ (|t| + |u|)ρ ≤ (m + K)ρ < g. Therefore
|gZ + W| < g·2^m ≤ q, and being divisible by q, gZ + W = 0. Then |gZ| = |W| < g forces Z = 0:
Σ_{j : a_j ∈ t} 2^j = Σ_{j : a_j ∈ u} 2^j. Binary expansions are unique, so
{j : a_j ∈ t} = {j : a_j ∈ u}; by disjointness both are empty. Thus t, u ⊆ D, contradicting
that D is dissociated. ∎

## 6. The step theorem

**Theorem 7.** Let m ≥ 1, K ≥ 0, J = 2^{m+4}(m + K), and let A be a finite set of integers
with |A| > 4mJ⁵. Then there are A₁ ⊆ A with |A₁| ≥ ⌊|A|/J⌋ and E ⊆ A with |E| = m such that
for every dissociated D ⊆ A₁ with |D| ≤ K: D ∩ E = ∅ and D ∪ E is dissociated.

*Proof.* Put B = 2^{m+3}(m+K), so J = 2B. Choose a prime
q > J² + 2^{m+3} + B + 2·max_{a∈A}|a|, and let

  ρ = ⌊q/B⌋, g = ⌊q/2^{m+1}⌋, M + 1 = J².

Arithmetic: g·2^{m+1} ≤ q; ρB ≤ q; ρ ≥ 1; q ≤ ρJ (because q < B(ρ+1) ≤ 2Bρ);
2ρ ≤ q; and (m+K)ρ < g. For the last one: 4·(m+K)ρ·2^{m+1} = ρB ≤ q < (g+1)2^{m+1}, so if
g ≤ (m+K)ρ we would get q < (m+K)ρ·2^{m+1} + 2^{m+1} ≤ q/4 + 2^{m+1}, i.e. q < 2^{m+3}.

Reduction mod q is injective on A (as q > 2 max|a|); let A′ ⊆ ℤ/q be the image, |A′| = |A|.
For j < m let c_j = 2^j g mod q and Bad_j = { r : N_{c_j}(r) ≤ |A|(M+1)/2 } (for the set A′);
by Corollary A, |Bad_j| ≤ 4J⁴q/|A|. For 1 ≤ s ≤ J (so s is invertible mod q, as J < q) the
set { r : sr ∈ Bad_j } has the same size. The union U of these sets over the Jm pairs (s, j)
has |U| ≤ Jm·4J⁴q/|A| < q because |A| > 4mJ⁵. Fix r ∉ U.

*Hits.* For all 1 ≤ s ≤ J and j < m: sr ∉ Bad_j, so by Corollary B there are a ∈ A and v ≡
sra − 2^j g with 2J²v² < q², i.e. 8B²v² < q², so |v|B < q and |v| ≤ ρ. Then sra ≡ v + 2^j g and
0 < v + 2^j g, 2(v + 2^j g) ≤ 2ρ + 2^m g ≤ 2^{m+1} g ≤ q (using ρ < g and 2 ≤ 2^m), so the
centered representative of sra is v + 2^j g: it is within ρ of 2^j g.

*Mass near 0.* By Lemma 5 (w = ρ), for every a ∈ A there is s(a) ∈ [1, J] such that the centered
representative of s(a)·r·a has absolute value < ρ (note 2ρ ≤ q). By pigeonhole some s ∈ [1, J]
is s(a) for at least ⌊|A|/J⌋ elements a; let A₁ be the set of these.

Now apply Lemma 6 with the multiplier sr, the elements a_j given by the hits for this s, and
any dissociated D ⊆ A₁ with |D| ≤ K (and with D = ∅ to get that the a_j are distinct, so
|E| = m). ∎

## 7. Iteration

**Proposition 8.** Let m, t ≥ 1 and J = 2^{m+4}(m + tm). For 0 ≤ i ≤ t, every finite set A of
integers with |A| ≥ (4mJ⁵ + 1)·J^i contains a dissociated subset with exactly i·m elements.

*Proof.* Induction on i; i = 0 is trivial. For i + 1 ≤ t apply Theorem 7 with K = tm:
|A₁| ≥ ⌊|A|/J⌋ ≥ (4mJ⁵+1)J^i, so A₁ contains a dissociated B₁ with |B₁| = im ≤ K, and B₁ ∪ E
is dissociated with (i+1)m elements. ∎

**Corollary 9.** If m, t ≥ 1 and n ≥ (4mJ⁵ + 1)J^t then f(n) ≥ tm. (Lemma 1 + Proposition 8.)

**Corollary 10.** For every t there is m₀ such that for m ≥ m₀ and n ≥ 2^{m(t+7)}: f(n) ≥ tm.

*Proof.* J = 2^m·(16(t+1)m) ≥ 4m + 1, so (4mJ⁵+1)J^t ≤ J^{t+6} = 2^{m(t+6)}(16(t+1)m)^{t+6}
≤ 2^{m(t+7)} once (16(t+1)m)^{t+6} ≤ 2^m, which holds for all large m. ∎

## 8. Conclusion

Let c > 0. Take t = ⌈14/c⌉, m₀ from Corollary 10, x = log₂ n and
m = ⌊(x − 1)/(t + 7)⌋. For n large m ≥ m₀ and 2^{m(t+7)} ≤ 2^{x} = n, so
f(n) ≥ tm ≥ t((x−1)/(t+7) − 1), whence

  x − f(n) ≤ 1 + t + 7(x−1)/(t+7) ≤ 1 + t + (c/2)x ≤ c·x

for x ≥ 2(t+1)/c, using c(t+7) ≥ 14. Together with Section 1, |f(n) − log₂ n| ≤ c·log₂ n for
all large n. Hence f(n) ~ log₂ n. ∎

## Remarks

* No attempt was made to optimize the error term; the proof as written gives
  f(n) ≥ (t/(t+7)) log₂ n − O_t(1) for each fixed t.
* Part ii (f(n) ≥ ⌊log₂ n⌋ for all n) is **not** addressed by this proof.
* A small numerical script (not included in this repository) tested Lemma 2, Lemma 4 and Lemma 6 numerically on random small cases.
