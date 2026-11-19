import E963.StepThm

/-!
# Erdős 963 — iteration of the step theorem and transfer from `ℝ` to `ℤ`
-/

open Finset

namespace Erdos963

/-- Iterating the step theorem `i ≤ t` times gives a dissociated set with `i * m` elements. -/
theorem iterate (m t J : ℕ) (hm : 1 ≤ m) (hJ : J = 2 ^ (m + 4) * (m + t * m)) :
    ∀ i ≤ t, ∀ A : Finset ℤ, (4 * m * J ^ 5 + 1) * J ^ i ≤ A.card →
      ∃ B ⊆ A, B.card = i * m ∧ AddDissociated (B : Set ℤ) := by
  classical
  have hJpos : 0 < J := by
    rw [hJ]; exact Nat.mul_pos (by positivity) (by omega)
  intro i
  induction i with
  | zero => intro _ A _; exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ i ih =>
    intro hi A hA
    have hbig : 4 * m * J ^ 5 < A.card := by
      have h1 : 1 ≤ J ^ (i + 1) := Nat.one_le_pow _ _ hJpos
      calc 4 * m * J ^ 5 < (4 * m * J ^ 5 + 1) * 1 := by omega
        _ ≤ (4 * m * J ^ 5 + 1) * J ^ (i + 1) := Nat.mul_le_mul_left _ h1
        _ ≤ A.card := hA
    obtain ⟨A₁, hA₁, hcard, E, hE, hEcard, hstep⟩ :=
      step A m (t * m) hm (by rw [← hJ]; exact hbig)
    rw [← hJ] at hcard
    have hA₁big : (4 * m * J ^ 5 + 1) * J ^ i ≤ A₁.card := by
      refine le_trans ?_ hcard
      rw [Nat.le_div_iff_mul_le hJpos]
      calc (4 * m * J ^ 5 + 1) * J ^ i * J = (4 * m * J ^ 5 + 1) * J ^ (i + 1) := by
            rw [pow_succ]; ring
        _ ≤ A.card := hA
    obtain ⟨B₁, hB₁, hB₁card, hB₁d⟩ := ih (by omega) A₁ hA₁big
    have hK : B₁.card ≤ t * m := by
      rw [hB₁card]; exact Nat.mul_le_mul_right _ (by omega)
    obtain ⟨hdisj, hdiss⟩ := hstep B₁ hB₁ hB₁d hK
    refine ⟨B₁ ∪ E, union_subset (hB₁.trans hA₁) hE, ?_, hdiss⟩
    rw [card_union_of_disjoint hdisj, hB₁card, hEcard]; ring

/-- A finite set of reals can be mapped injectively to the integers in such a way that
dissociated sets pull back to dissociated sets. -/
theorem exists_int_model (A : Finset ℝ) :
    ∃ φ : ℝ → ℤ, Set.InjOn φ A ∧
      ∀ B ⊆ A, AddDissociated ((B.image φ : Finset ℤ) : Set ℤ) →
        AddDissociated (B : Set ℝ) := by
  classical
  set S : Finset ℝ := ((A ×ˢ A).image fun p ↦ p.1 - p.2).filter (· ≠ 0) with hS
  obtain ⟨g, hg⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ) (M := ℝ)
    (fun i : S ↦ (i : ℝ)) (fun i ↦ (mem_filter.1 i.2).2)
  have hginj : Set.InjOn g A := by
    intro x hx y hy hxy
    by_contra hne
    have hmem : x - y ∈ S :=
      mem_filter.2 ⟨mem_image.2 ⟨(x, y), mem_product.2 ⟨hx, hy⟩, rfl⟩, sub_ne_zero.2 hne⟩
    apply hg ⟨_, hmem⟩
    simp only [map_sub, hxy, sub_self]
  set N : ℕ := ∏ a ∈ A, (g a).den with hN
  have hint : ∀ a ∈ A, ∃ z : ℤ, (z : ℚ) = N * g a := by
    intro a ha
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a ↦ (g a).den) ha
    refine ⟨c * (g a).num, ?_⟩
    rw [hN, hc]
    push_cast
    have := Rat.mul_den_eq_num (g a)
    rw [← this]; ring
  set φ : ℝ → ℤ := fun x ↦ ⌊(N : ℚ) * g x⌋ with hφ
  have hφ' : ∀ a ∈ A, (φ a : ℚ) = N * g a := by
    intro a ha
    obtain ⟨z, hz⟩ := hint a ha
    simp only [hφ]
    rw [← hz, Int.floor_intCast]
  have hNpos : (0 : ℚ) < N := by
    have : 0 < N := Finset.prod_pos fun a _ ↦ (g a).den_pos
    exact_mod_cast this
  have hφinj : Set.InjOn φ A := by
    intro x hx y hy hxy
    apply hginj hx hy
    have : (N : ℚ) * g x = N * g y := by rw [← hφ' x hx, ← hφ' y hy, hxy]
    exact mul_left_cancel₀ hNpos.ne' this
  refine ⟨φ, hφinj, ?_⟩
  intro B hB hdiss t ht u hu hsum
  have ht' : t ⊆ B := coe_subset.1 ht
  have hu' : u ⊆ B := coe_subset.1 hu
  have hsumφ : ∀ s : Finset ℝ, s ⊆ B →
      ((∑ y ∈ s.image φ, y : ℤ) : ℚ) = N * g (∑ x ∈ s, x) := by
    intro s hs
    rw [sum_image (fun x hx y hy h ↦ hφinj (hB (hs hx)) (hB (hs hy)) h), Int.cast_sum,
      map_sum, mul_sum]
    exact sum_congr rfl fun x hx ↦ hφ' x (hB (hs hx))
  have heq : ∑ y ∈ t.image φ, y = ∑ y ∈ u.image φ, y := by
    have h1 : ((∑ y ∈ t.image φ, y : ℤ) : ℚ) = ((∑ y ∈ u.image φ, y : ℤ) : ℚ) := by
      rw [hsumφ t ht', hsumφ u hu']
      have : ∑ x ∈ t, x = ∑ x ∈ u, x := hsum
      rw [this]
    exact_mod_cast h1
  have himg : t.image φ = u.image φ :=
    hdiss (coe_subset.2 (image_subset_image ht')) (coe_subset.2 (image_subset_image hu')) heq
  ext x
  constructor
  · intro hx
    have h1 : φ x ∈ u.image φ := himg ▸ mem_image_of_mem φ hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 h1
    have h2 := hφinj (hB (hu' hy)) (hB (ht' hx)) hyx
    rwa [← h2]
  · intro hx
    have h1 : φ x ∈ t.image φ := himg ▸ mem_image_of_mem φ hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 h1
    have h2 := hφinj (hB (ht' hy)) (hB (hu' hx)) hyx
    rwa [← h2]

/-- The lower bound for `f` coming out of the iteration. -/
theorem f_lower (m t n : ℕ) (hm : 1 ≤ m)
    (hn : (4 * m * (2 ^ (m + 4) * (m + t * m)) ^ 5 + 1) * (2 ^ (m + 4) * (m + t * m)) ^ t ≤ n) :
    t * m ≤ f n := by
  classical
  refine le_f fun A hA ↦ ?_
  obtain ⟨φ, hφinj, hφ⟩ := exists_int_model A
  have hA' : (A.image φ).card = n := by rw [card_image_of_injOn hφinj, hA]
  obtain ⟨B', hB', hB'card, hB'd⟩ :=
    iterate m t _ hm rfl t le_rfl (A.image φ) (by rw [hA']; exact hn)
  obtain ⟨B, hB, rfl⟩ := subset_image_iff.1 hB'
  refine ⟨B, hB, ?_, hφ B hB hB'd⟩
  rw [← hB'card]
  exact card_image_le

end Erdos963
