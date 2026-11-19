import E963.Kernel

/-!
# Erdős 963 — the step lemma

Given a finite set `A` of integers we find a dilation `x ↦ ρ x` modulo a prime `q` such that
many elements of `A` are sent close to `0` and, for each `j < m`, some element of `A` is sent
close to `2 ^ j * g`.
-/

open Finset

namespace Erdos963

lemma bad_card {q : ℕ} [NeZero q] [Fact q.Prime] (A : Finset (ZMod q)) (M : ℕ) (hM : M + 1 ≤ q)
    (c : ZMod q) :
    (((univ : Finset (ZMod q)).filter
        fun r ↦ cnt A M c r ≤ A.card * ((M : ℝ) + 1) / 2).card : ℝ) * A.card
      ≤ 4 * ((M : ℝ) + 1) ^ 2 * q := by
  classical
  set Bad := (univ : Finset (ZMod q)).filter
    fun r ↦ cnt A M c r ≤ A.card * ((M : ℝ) + 1) / 2 with hBad
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, mul_zero]; positivity
  have hn : (0 : ℝ) < A.card := by exact_mod_cast hpos
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have h1 : ∑ _r ∈ Bad, (A.card * ((M : ℝ) + 1) / 2) ^ 2 ≤
      ∑ r ∈ Bad, (cnt A M c r - A.card * (M + 1)) ^ 2 := by
    refine sum_le_sum fun r hr ↦ ?_
    have hr' : cnt A M c r ≤ A.card * ((M : ℝ) + 1) / 2 := (mem_filter.1 hr).2
    have h0 : 0 ≤ A.card * ((M : ℝ) + 1) / 2 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.2 hr')
      (sub_nonneg.2 (hr'.trans (le_mul_of_one_le_left h0 (by norm_num : (1 : ℝ) ≤ 3))))]
  have h2 : ∑ r ∈ Bad, (cnt A M c r - A.card * (M + 1)) ^ 2 ≤
      ∑ r : ZMod q, (cnt A M c r - A.card * (M + 1)) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _
  have h3 := second_moment A M hM c
  rw [sum_const, nsmul_eq_mul] at h1
  have h4 : (Bad.card : ℝ) * (A.card * ((M : ℝ) + 1) / 2) ^ 2 ≤
      ((M : ℝ) + 1) ^ 4 * q * A.card := h1.trans (h2.trans h3)
  have h5 : ((Bad.card : ℝ) * A.card) * (A.card * ((M : ℝ) + 1) ^ 2 / 4) ≤
      (4 * ((M : ℝ) + 1) ^ 2 * q) * (A.card * ((M : ℝ) + 1) ^ 2 / 4) := by
    calc ((Bad.card : ℝ) * A.card) * (A.card * ((M : ℝ) + 1) ^ 2 / 4)
        = (Bad.card : ℝ) * (A.card * ((M : ℝ) + 1) / 2) ^ 2 := by ring
      _ ≤ ((M : ℝ) + 1) ^ 4 * q * A.card := h4
      _ = (4 * ((M : ℝ) + 1) ^ 2 * q) * (A.card * ((M : ℝ) + 1) ^ 2 / 4) := by ring
  exact le_of_mul_le_mul_right h5 (by positivity)

lemma hit_of_cnt {q : ℕ} [NeZero q] (A : Finset (ZMod q)) (M : ℕ) (c r : ZMod q)
    (h : A.card * ((M : ℝ) + 1) / 2 < cnt A M c r) :
    ∃ a ∈ A, ∃ v : ℤ, (v : ZMod q) = r * a - c ∧ 2 * ((M : ℤ) + 1) * v ^ 2 < (q : ℤ) ^ 2 := by
  by_contra hcon
  push Not at hcon
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have : cnt A M c r ≤ A.card * ((M : ℝ) + 1) / 2 := by
    unfold cnt
    calc ∑ a ∈ A, ker M (r * a - c) ≤ ∑ _a ∈ A, ((M : ℝ) + 1) / 2 := by
          refine sum_le_sum fun a ha ↦ ?_
          have hv := hcon a ha (r * a - c).valMinAbs (ZMod.coe_valMinAbs _)
          have hvR : (q : ℝ) ^ 2 ≤ 2 * ((M : ℝ) + 1) * ((r * a - c).valMinAbs : ℝ) ^ 2 := by
            exact_mod_cast hv
          have hv0 : ((r * a - c).valMinAbs : ℝ) ≠ 0 := by
            intro h0; rw [h0] at hvR; nlinarith
          have hx : r * a - c ≠ 0 := by
            intro h0; apply hv0; rw [h0, ZMod.valMinAbs_zero]; simp
          refine (ker_le M hx).trans ?_
          have hv2 : 0 < ((r * a - c).valMinAbs : ℝ) ^ 2 := by positivity
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
      _ = A.card * ((M : ℝ) + 1) / 2 := by rw [sum_const, nsmul_eq_mul]; ring
  linarith

lemma dirichlet {q : ℕ} [NeZero q] (w J : ℕ) (hJ : q ≤ w * J) (x : ZMod q) :
    ∃ s ∈ Icc 1 J, ∃ v : ℤ, (v : ZMod q) = (s : ZMod q) * x ∧ |v| < w := by
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; simp only [zero_mul, nonpos_iff_eq_zero] at hJ; exact absurd hJ (NeZero.ne q)
    · exact h
  have hmaps : ∀ t ∈ range (J + 1), (((t : ZMod q) * x).val / w) ∈ range J := by
    intro t _
    rw [mem_range]
    have := ZMod.val_lt ((t : ZMod q) * x)
    exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le this hJ)
  obtain ⟨t, ht, t', ht', hne, heq⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to (by simp) hmaps
  wlog hlt : t < t' generalizing t t'
  · exact this t' ht' t ht hne.symm heq.symm (lt_of_le_of_ne (not_lt.1 hlt) hne.symm)
  refine ⟨t' - t, ?_, (((t' : ZMod q) * x).val : ℤ) - (((t : ZMod q) * x).val : ℤ), ?_, ?_⟩
  · rw [mem_Icc]; rw [mem_range] at ht ht'; omega
  · push_cast [Nat.cast_sub hlt.le]
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; ring
  · have h1 := Nat.div_add_mod ((t' : ZMod q) * x).val w
    have h2 := Nat.div_add_mod ((t : ZMod q) * x).val w
    have h3 := Nat.mod_lt ((t' : ZMod q) * x).val hw
    have h4 := Nat.mod_lt ((t : ZMod q) * x).val hw
    rw [heq] at h2
    generalize w * (((t' : ZMod q) * x).val / w) = z at h1 h2
    rw [abs_lt]
    constructor <;> omega

/-- The lifting lemma: elements sent near `2 ^ j * g` together with a dissociated set of
elements sent near `0` form a dissociated set. -/
lemma lift {q : ℕ} [NeZero q] (r : ZMod q) (g ρ m K : ℕ) (h1 : (m + K) * ρ < g)
    (h2 : g * 2 ^ (m + 1) ≤ q) (a : ℕ → ℤ) (D : Finset ℤ)
    (hD : AddDissociated (D : Set ℤ)) (hK : D.card ≤ K)
    (hDν : ∀ d ∈ D, |(r * (d : ZMod q)).valMinAbs| ≤ ρ)
    (hEν : ∀ j < m, |(r * (a j : ZMod q)).valMinAbs - 2 ^ j * g| ≤ ρ) :
    Set.InjOn a (range m) ∧ (∀ j < m, a j ∉ D) ∧
      AddDissociated ((D ∪ (range m).image a : Finset ℤ) : Set ℤ) := by
  classical
  set ν : ℤ → ℤ := fun x ↦ (r * (x : ZMod q)).valMinAbs with hν
  have hg0 : (0 : ℤ) ≤ g := Int.natCast_nonneg g
  have hρ0 : (0 : ℤ) ≤ ρ := Int.natCast_nonneg ρ
  have h1' : ((m : ℤ) + K) * ρ < g := by exact_mod_cast h1
  -- injectivity
  have hinj : Set.InjOn a (range m) := by
    have key : ∀ j j', j < m → j' < m → j < j' → a j ≠ a j' := by
      intro j j' hj hj' hlt heq
      have e1 := hEν j hj
      have e2 := hEν j' hj'
      rw [← heq] at e2
      rw [abs_le] at e1 e2
      have hp : (2 : ℤ) * 2 ^ j ≤ 2 ^ j' := by
        rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hlt
      have hp1 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have hm2 : (2 : ℤ) ≤ (m : ℤ) + K := by
        have : 2 ≤ m := by omega
        have h3 : (2 : ℤ) ≤ m := by exact_mod_cast this
        have h4 : (0 : ℤ) ≤ K := Int.natCast_nonneg K
        linarith
      have h5 : (2 : ℤ) * ρ ≤ ((m : ℤ) + K) * ρ := mul_le_mul_of_nonneg_right hm2 hρ0
      have h6 : (2 : ℤ) * 2 ^ j * g ≤ 2 ^ j' * g := mul_le_mul_of_nonneg_right hp hg0
      have h7 : (1 : ℤ) * g ≤ 2 ^ j * g := mul_le_mul_of_nonneg_right hp1 hg0
      linarith
    intro j hj j' hj' heq
    rw [coe_range, Set.mem_Iio] at hj hj'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key j j' hj hj' h heq
    · exact key j' j hj' hj h heq.symm
  -- the `a j` are not in `D`
  have hnot : ∀ j < m, a j ∉ D := by
    intro j hj hmem
    have e1 := hEν j hj
    have e2 := hDν _ hmem
    rw [abs_le] at e1 e2
    have hp1 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hK1 : 1 ≤ K := (Finset.card_pos.2 ⟨_, hmem⟩).trans_le hK
    have hm2 : (2 : ℤ) ≤ (m : ℤ) + K := by
      have h3 : (1 : ℤ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      have h4 : (1 : ℤ) ≤ K := by exact_mod_cast hK1
      linarith
    have h5 : (2 : ℤ) * ρ ≤ ((m : ℤ) + K) * ρ := mul_le_mul_of_nonneg_right hm2 hρ0
    have h7 : (1 : ℤ) * g ≤ 2 ^ j * g := mul_le_mul_of_nonneg_right hp1 hg0
    linarith
  refine ⟨hinj, hnot, ?_⟩
  set E := (range m).image a with hE
  by_contra hcon
  rw [not_addDissociated_iff_exists_disjoint] at hcon
  obtain ⟨t, u, ht, hu, hdisj, hne, hsum⟩ := hcon
  rw [coe_subset] at ht hu
  set β : ℤ → ℕ := fun x ↦ ∑ j ∈ (range m).filter (fun j ↦ a j = x), 2 ^ j with hβ
  have hβsum : ∀ s : Finset ℤ, ∑ x ∈ s, β x = ∑ j ∈ (range m).filter (fun j ↦ a j ∈ s), 2 ^ j :=
    fun s ↦ sum_fiberwise_eq_sum_filter (range m) s a fun j ↦ 2 ^ j
  have hβlt : ∀ s : Finset ℤ, ∑ x ∈ s, β x < 2 ^ m := by
    intro s
    rw [hβsum]
    exact Nat.geomSum_lt le_rfl fun k hk ↦ mem_range.1 (mem_filter.1 hk).1
  -- decomposition of ν
  have hdec : ∀ x ∈ D ∪ E, |ν x - g * (β x : ℤ)| ≤ ρ := by
    intro x hx
    by_cases hxD : x ∈ D
    · have : β x = 0 := by
        rw [hβ]
        apply sum_eq_zero
        intro j hj
        rw [mem_filter, mem_range] at hj
        exact absurd (hj.2 ▸ hxD) (hnot j hj.1)
      rw [this]; simpa using hDν x hxD
    · have hxE : x ∈ E := (mem_union.1 hx).resolve_left hxD
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hxE
      have hj' := mem_range.1 hj
      have : (range m).filter (fun j' ↦ a j' = a j) = {j} := by
        ext j'
        rw [mem_filter, mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩; exact hinj h1 hj h2
        · rintro rfl; exact ⟨hj, rfl⟩
      have hb : β (a j) = 2 ^ j := by rw [hβ]; simp only; rw [this, sum_singleton]
      rw [hb]
      have := hEν j hj'
      push_cast
      rwa [mul_comm]
  -- congruence
  have hcong : (q : ℤ) ∣ ∑ x ∈ t, ν x - ∑ x ∈ u, ν x := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp only [hν, ZMod.coe_valMinAbs]
    rw [← mul_sum, ← mul_sum, ← Int.cast_sum, ← Int.cast_sum, hsum, sub_self]
  -- error terms
  set e : ℤ → ℤ := fun x ↦ ν x - g * (β x : ℤ) with he
  have hsplit : ∀ s : Finset ℤ, ∑ x ∈ s, ν x = g * ((∑ x ∈ s, β x : ℕ) : ℤ) + ∑ x ∈ s, e x := by
    intro s
    rw [he, sum_sub_distrib, Nat.cast_sum, mul_sum]; ring
  have herr : ∀ s : Finset ℤ, s ⊆ D ∪ E → |∑ x ∈ s, e x| ≤ s.card * ρ := by
    intro s hs
    calc |∑ x ∈ s, e x| ≤ ∑ x ∈ s, |e x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ s, (ρ : ℤ) := sum_le_sum fun x hx ↦ hdec x (hs hx)
      _ = s.card * ρ := by rw [sum_const, nsmul_eq_mul]
  have hcard : ((t.card : ℤ) + u.card) * ρ ≤ ((m : ℤ) + K) * ρ := by
    refine mul_le_mul_of_nonneg_right ?_ hρ0
    have h3 : t.card + u.card ≤ m + K := by
      rw [← card_union_of_disjoint hdisj]
      calc (t ∪ u).card ≤ (D ∪ E).card := card_le_card (union_subset ht hu)
        _ ≤ D.card + E.card := card_union_le _ _
        _ ≤ K + m := add_le_add hK (card_image_le.trans (card_range m).le)
        _ = m + K := add_comm _ _
    exact_mod_cast h3
  set Z : ℤ := ((∑ x ∈ t, β x : ℕ) : ℤ) - ((∑ x ∈ u, β x : ℕ) : ℤ) with hZ
  set W : ℤ := ∑ x ∈ t, e x - ∑ x ∈ u, e x with hW
  have hW' : |W| < g := by
    have h3 := herr t ht
    have h4 := herr u hu
    have : |W| ≤ |∑ x ∈ t, e x| + |∑ x ∈ u, e x| := abs_sub _ _
    have h5 : (t.card : ℤ) * ρ + u.card * ρ = ((t.card : ℤ) + u.card) * ρ := by ring
    linarith
  have hZW : ∑ x ∈ t, ν x - ∑ x ∈ u, ν x = g * Z + W := by
    rw [hsplit t, hsplit u, hZ, hW]; ring
  have hZabs : |Z| ≤ 2 ^ m - 1 := by
    have h3 : ((∑ x ∈ t, β x : ℕ) : ℤ) < 2 ^ m := by exact_mod_cast hβlt t
    have h4 : ((∑ x ∈ u, β x : ℕ) : ℤ) < 2 ^ m := by exact_mod_cast hβlt u
    have h5 : (0 : ℤ) ≤ ((∑ x ∈ t, β x : ℕ) : ℤ) := Int.natCast_nonneg _
    have h6 : (0 : ℤ) ≤ ((∑ x ∈ u, β x : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [hZ, abs_le]; constructor <;> linarith
  have hzero : (g : ℤ) * Z + W = 0 := by
    rw [← hZW]
    refine Int.eq_zero_of_abs_lt_dvd hcong ?_
    rw [hZW]
    have h3 : |(g : ℤ) * Z| ≤ g * (2 ^ m - 1) := by
      rw [abs_mul, abs_of_nonneg hg0]; exact mul_le_mul_of_nonneg_left hZabs hg0
    have h4 : ((g * 2 ^ (m + 1) : ℕ) : ℤ) ≤ q := by exact_mod_cast h2
    have h5 : (g : ℤ) * 2 ^ m ≤ ((g * 2 ^ (m + 1) : ℕ) : ℤ) := by
      push_cast
      rw [pow_succ]
      have : (0 : ℤ) ≤ (g : ℤ) * 2 ^ m := by positivity
      linarith
    have := abs_add_le ((g : ℤ) * Z) W
    linarith
  have hZ0 : Z = 0 := by
    by_contra hZne
    have h3 : (1 : ℤ) ≤ |Z| := Int.one_le_abs hZne
    have h4 : (g : ℤ) * 1 ≤ g * |Z| := mul_le_mul_of_nonneg_left h3 hg0
    have h5 : |(g : ℤ) * Z| = |W| := by
      have : (g : ℤ) * Z = -W := by linarith
      rw [this, abs_neg]
    rw [abs_mul, abs_of_nonneg hg0] at h5
    linarith
  have hβeq : ∑ x ∈ t, β x = ∑ x ∈ u, β x := by
    have : ((∑ x ∈ t, β x : ℕ) : ℤ) = ((∑ x ∈ u, β x : ℕ) : ℤ) := by
      rw [hZ] at hZ0; linarith
    exact_mod_cast this
  rw [hβsum t, hβsum u] at hβeq
  have hfil := Finset.geomSum_injective le_rfl hβeq
  have hnone : ∀ j < m, a j ∉ t ∧ a j ∉ u := by
    intro j hj
    have hiff : a j ∈ t ↔ a j ∈ u := by
      have := Finset.ext_iff.1 hfil j
      simpa [mem_filter, mem_range, hj] using this
    constructor
    · intro h; exact (disjoint_left.1 hdisj h) (hiff.1 h)
    · intro h; exact (disjoint_left.1 hdisj (hiff.2 h)) h
  have htD : t ⊆ D := by
    intro x hx
    rcases mem_union.1 (ht hx) with h | h
    · exact h
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 h
      exact absurd hx (hnone j (mem_range.1 hj)).1
  have huD : u ⊆ D := by
    intro x hx
    rcases mem_union.1 (hu hx) with h | h
    · exact h
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 h
      exact absurd hx (hnone j (mem_range.1 hj)).2
  exact hne (hD (coe_subset.2 htD) (coe_subset.2 huD) hsum)

end Erdos963
