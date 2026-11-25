module

public import E963.Iterate

/-!
# Erdős 963 — the upper bound from `A = {1, …, n}`
-/

@[expose] public section

open Finset

namespace Erdos963

/-- A dissociated subset `B` of `{1, …, n}` satisfies `2 ^ |B| ≤ |B| n + 1`. -/
theorem diss_Icc_bound (n : ℕ) (B : Finset ℝ)
    (hB : B ⊆ (Icc 1 n).image (Nat.cast : ℕ → ℝ))
    (hd : AddDissociated (B : Set ℝ)) : 2 ^ B.card ≤ B.card * n + 1 := by
  classical
  obtain ⟨B₀, hB₀, rfl⟩ := subset_image_iff.1 hB
  rw [card_image_of_injective _ Nat.cast_injective]
  have key : (B₀.powerset).card ≤ (range (B₀.card * n + 1)).card := by
    refine card_le_card_of_injOn (fun t ↦ ∑ y ∈ t, y) ?_ ?_
    · intro t ht
      have ht' : t ⊆ B₀ := mem_powerset.1 ht
      have : ∑ y ∈ t, y < B₀.card * n + 1 := by
        rw [Nat.lt_succ_iff]
        calc ∑ y ∈ t, y ≤ ∑ _y ∈ t, n :=
              sum_le_sum fun y hy ↦ (mem_Icc.1 (hB₀ (ht' hy))).2
          _ = t.card * n := by rw [sum_const, smul_eq_mul]
          _ ≤ B₀.card * n := Nat.mul_le_mul_right _ (card_le_card ht')
      exact mem_range.2 this
    · intro t ht u hu h
      have ht' : t ⊆ B₀ := mem_powerset.1 ht
      have hu' : u ⊆ B₀ := mem_powerset.1 hu
      have h0 : ∑ y ∈ t, y = ∑ y ∈ u, y := h
      have h' : ∑ x ∈ t.image (Nat.cast : ℕ → ℝ), x = ∑ x ∈ u.image (Nat.cast : ℕ → ℝ), x := by
        rw [sum_image (Nat.cast_injective.injOn), sum_image (Nat.cast_injective.injOn),
          ← Nat.cast_sum, ← Nat.cast_sum, h0]
      have := hd (coe_subset.2 (image_subset_image ht')) (coe_subset.2 (image_subset_image hu')) h'
      exact Finset.image_injective Nat.cast_injective this
  rwa [card_powerset, card_range] at key

/-- The upper bound `f n ≤ log₂ (n log₂ (n² + 1) + 1)`. -/
theorem f_upper (n : ℕ) : f n ≤ Nat.log 2 (Nat.log 2 (n * n + 1) * n + 1) := by
  classical
  refine f_le ((Icc 1 n).image (Nat.cast : ℕ → ℝ))
    (by rw [card_image_of_injective _ Nat.cast_injective]; simp) fun B hB hd ↦ ?_
  have h1 := diss_Icc_bound n B hB hd
  have hBn : B.card ≤ n := by
    calc B.card ≤ ((Icc 1 n).image (Nat.cast : ℕ → ℝ)).card := card_le_card hB
      _ ≤ (Icc 1 n).card := card_image_le
      _ = n := by simp
  have h2 : 2 ^ B.card ≤ n * n + 1 :=
    h1.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hBn) 1)
  have h3 : B.card ≤ Nat.log 2 (n * n + 1) := Nat.le_log_of_pow_le (by norm_num) h2
  have h4 : 2 ^ B.card ≤ Nat.log 2 (n * n + 1) * n + 1 :=
    h1.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ h3) 1)
  exact Nat.le_log_of_pow_le (by norm_num) h4

end Erdos963
