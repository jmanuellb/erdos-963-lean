module

public import E963.Step

/-!
# Erdős 963 — the step theorem for finite sets of integers
-/

@[expose] public section

open Finset

namespace Erdos963

/-- **Step theorem.** If `A` is a large finite set of integers then there are a subset `A₁` of
density at least `1 / (2 ^ (m + 4) * (m + K))` and `m` elements `E` of `A` which can be added
to every dissociated subset of `A₁` with at most `K` elements. -/
theorem step (A : Finset ℤ) (m K : ℕ) (hm : 1 ≤ m)
    (hn : 4 * m * (2 ^ (m + 4) * (m + K)) ^ 5 < A.card) :
    ∃ A₁ ⊆ A, A.card / (2 ^ (m + 4) * (m + K)) ≤ A₁.card ∧ ∃ E ⊆ A, E.card = m ∧
      ∀ D ⊆ A₁, AddDissociated (D : Set ℤ) → D.card ≤ K →
        Disjoint D E ∧ AddDissociated ((D ∪ E : Finset ℤ) : Set ℤ) := by
  classical
  set B := 2 ^ (m + 3) * (m + K) with hB
  set J := 2 ^ (m + 4) * (m + K) with hJ
  have hJB : J = 2 * B := by rw [hJ, hB]; ring
  have hmK : 0 < m + K := by omega
  have hBpos : 0 < B := by positivity
  have hJpos : 0 < J := by positivity
  have hB2 : 2 ≤ B := by
    have : 2 ^ 1 ≤ 2 ^ (m + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 = 2 ^ 1 * 1 := by norm_num
      _ ≤ 2 ^ (m + 3) * (m + K) := Nat.mul_le_mul this hmK
  have hB3 : 2 ^ (m + 3) ≤ B := Nat.le_mul_of_pos_right _ hmK
  set S := A.sup Int.natAbs with hS
  obtain ⟨J2, hJ2⟩ : ∃ J2, J2 = J ^ 2 := ⟨_, rfl⟩
  have hJ2pos : 0 < J2 := by rw [hJ2]; positivity
  obtain ⟨q, hqge, hqp⟩ :=
    Nat.exists_infinite_primes (J2 + B + 2 * S + 1)
  have : Fact q.Prime := ⟨hqp⟩
  have : NeZero q := ⟨hqp.ne_zero⟩
  set ρ := q / B with hρ
  set g := q / 2 ^ (m + 1) with hg
  obtain ⟨M, hM1'⟩ : ∃ M, M + 1 = J2 := ⟨J2 - 1, Nat.sub_add_cancel hJ2pos⟩
  have hM1 : M + 1 = J ^ 2 := hM1'.trans hJ2
  have hMq : M + 1 ≤ q := by omega
  have hJq : J < q := by
    have : J ≤ J2 := hJ2 ▸ Nat.le_self_pow (by norm_num) J
    omega
  -- arithmetic of the parameters
  have hg2 : g * 2 ^ (m + 1) ≤ q := Nat.div_mul_le_self _ _
  have hρB : ρ * B ≤ q := Nat.div_mul_le_self _ _
  have hρ1 : 1 ≤ ρ := Nat.div_pos (by omega) hBpos
  have h1 : (m + K) * ρ < g := by
    by_contra hcon
    push Not at hcon
    set P := 2 ^ (m + 1) with hP
    have hPpos : 0 < P := by positivity
    have h4P : 2 ^ (m + 3) = 4 * P := by rw [hP]; ring
    have hX : 4 * ((m + K) * ρ * P) ≤ q := by
      calc 4 * ((m + K) * ρ * P) = ρ * B := by rw [hB, h4P]; ring
        _ ≤ q := hρB
    have hlt : q < P * (g + 1) := Nat.lt_mul_div_succ q hPpos
    have hle : P * (g + 1) ≤ (m + K) * ρ * P + P := by
      calc P * (g + 1) ≤ P * ((m + K) * ρ + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (m + K) * ρ * P + P := by ring
    have hq4 : 4 * P ≤ q := by
      have : 4 * P ≤ B := h4P ▸ hB3
      omega
    generalize (m + K) * ρ * P = X at hX hle
    generalize P * (g + 1) = Y at hlt hle
    omega
  have hρg : ρ < g := by
    calc ρ = 1 * ρ := (one_mul _).symm
      _ ≤ (m + K) * ρ := Nat.mul_le_mul_right _ hmK
      _ < g := h1
  have hwJ : q ≤ ρ * J := by
    have h3 : q < B * (ρ + 1) := Nat.lt_mul_div_succ q hBpos
    have h4 : ρ * J = 2 * (B * ρ) := by rw [hJB]; ring
    have h5 : B * (ρ + 1) = B * ρ + B := by ring
    have h6 : B ≤ B * ρ := Nat.le_mul_of_pos_right _ hρ1
    omega
  have h2ρq : 2 * ρ ≤ q := by
    calc 2 * ρ = ρ * 2 := mul_comm _ _
      _ ≤ ρ * B := Nat.mul_le_mul_left _ hB2
      _ ≤ q := hρB
  -- the cast is injective on `A`
  have hinjA : Set.InjOn (Int.cast : ℤ → ZMod q) A := by
    intro x hx y hy hxy
    have hx' : x.natAbs ≤ S := Finset.le_sup (f := Int.natAbs) hx
    have hy' : y.natAbs ≤ S := Finset.le_sup (f := Int.natAbs) hy
    have hdvd : (q : ℤ) ∣ y - x := (ZMod.intCast_eq_intCast_iff_dvd_sub x y q).1 hxy
    have habs : |y - x| < q := by
      have h3 : |y - x| ≤ |y| + |x| := abs_sub _ _
      have h4 : |x| = (x.natAbs : ℤ) := Int.abs_eq_natAbs x
      have h5 : |y| = (y.natAbs : ℤ) := Int.abs_eq_natAbs y
      have h6 : ((x.natAbs : ℕ) : ℤ) ≤ S := by exact_mod_cast hx'
      have h7 : ((y.natAbs : ℕ) : ℤ) ≤ S := by exact_mod_cast hy'
      have h8 : ((2 * S + 1 : ℕ) : ℤ) ≤ q := by exact_mod_cast (by omega : 2 * S + 1 ≤ q)
      push_cast at h8
      linarith
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    linarith
  set A' : Finset (ZMod q) := A.image (Int.cast : ℤ → ZMod q) with hA'
  have hA'card : A'.card = A.card := card_image_of_injOn hinjA
  set c : ℕ → ZMod q := fun j ↦ ((2 ^ j * g : ℕ) : ZMod q) with hc
  set Bad : ℕ → Finset (ZMod q) := fun j ↦ (univ : Finset (ZMod q)).filter
    fun r ↦ cnt A' M (c j) r ≤ A'.card * ((M : ℝ) + 1) / 2 with hBad
  have hbad : ∀ j, ((Bad j).card : ℝ) * A.card ≤ 4 * (J : ℝ) ^ 4 * q := by
    intro j
    have h := bad_card A' M hMq (c j)
    have hMJ : (M : ℝ) + 1 = (J : ℝ) ^ 2 := by exact_mod_cast hM1
    calc ((Bad j).card : ℝ) * A.card = ((Bad j).card : ℝ) * A'.card := by rw [hA'card]
      _ ≤ 4 * ((M : ℝ) + 1) ^ 2 * q := h
      _ = 4 * (J : ℝ) ^ 4 * q := by rw [hMJ]; ring
  have hsne : ∀ s ∈ Icc 1 J, (s : ZMod q) ≠ 0 := by
    intro s hs h0
    rw [mem_Icc] at hs
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by omega) h0
    omega
  set U : Finset (ZMod q) := (Icc 1 J ×ˢ range m).biUnion
    fun p ↦ (univ : Finset (ZMod q)).filter fun r ↦ (p.1 : ZMod q) * r ∈ Bad p.2 with hU
  have hpiece : ∀ p ∈ Icc 1 J ×ˢ range m,
      ((univ : Finset (ZMod q)).filter fun r ↦ (p.1 : ZMod q) * r ∈ Bad p.2).card ≤
        (Bad p.2).card := by
    intro p hp
    have hs := hsne p.1 (mem_product.1 hp).1
    refine card_le_card_of_injOn (fun r ↦ (p.1 : ZMod q) * r) ?_ ?_
    · intro r hr
      exact (mem_filter.1 hr).2
    · intro r _ r' _ h
      exact mul_left_cancel₀ hs h
  have hUcard : (U.card : ℝ) * A.card ≤ (J * m : ℕ) * (4 * (J : ℝ) ^ 4 * q) := by
    have h3 : U.card ≤ ∑ p ∈ Icc 1 J ×ˢ range m, (Bad p.2).card :=
      card_biUnion_le.trans (sum_le_sum hpiece)
    have h4 : (U.card : ℝ) ≤ ∑ p ∈ Icc 1 J ×ˢ range m, ((Bad p.2).card : ℝ) := by
      exact_mod_cast h3
    calc (U.card : ℝ) * A.card
        ≤ (∑ p ∈ Icc 1 J ×ˢ range m, ((Bad p.2).card : ℝ)) * A.card :=
          mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _)
      _ = ∑ p ∈ Icc 1 J ×ˢ range m, ((Bad p.2).card : ℝ) * A.card := sum_mul _ _ _
      _ ≤ ∑ _p ∈ Icc 1 J ×ˢ range m, 4 * (J : ℝ) ^ 4 * q := sum_le_sum fun p _ ↦ hbad p.2
      _ = (J * m : ℕ) * (4 * (J : ℝ) ^ 4 * q) := by
          rw [sum_const, nsmul_eq_mul, card_product, Nat.card_Icc, card_range]
          simp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hUq : U.card < q := by
    by_contra hcon
    push Not at hcon
    have h3 : (q : ℝ) ≤ U.card := by exact_mod_cast hcon
    have h4 : ((4 * m * J ^ 5 : ℕ) : ℝ) < A.card := by exact_mod_cast hn
    push_cast at h4 hUcard
    have h5 : (q : ℝ) * A.card ≤ U.card * A.card :=
      mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
    have h6 : (J : ℝ) * m * (4 * (J : ℝ) ^ 4 * q) = (4 * m * (J : ℝ) ^ 5) * q := by ring
    have h7 : (4 * m * (J : ℝ) ^ 5) * q < A.card * q := mul_lt_mul_of_pos_right h4 hq0
    linarith
  obtain ⟨r, hr⟩ : ∃ r : ZMod q, r ∉ U := by
    by_contra hcon
    push Not at hcon
    have : U = univ := eq_univ_iff_forall.2 hcon
    rw [this, card_univ, ZMod.card] at hUq
    exact lt_irrefl _ hUq
  -- hits
  have hits : ∀ s ∈ Icc 1 J, ∀ j, j < m → ∃ a, a ∈ A ∧
      |((s : ZMod q) * r * (a : ZMod q)).valMinAbs - 2 ^ j * g| ≤ ρ := by
    intro s hs j hj
    have hnb : (s : ZMod q) * r ∉ Bad j := by
      intro hmem
      apply hr
      rw [hU, mem_biUnion]
      exact ⟨(s, j), mem_product.2 ⟨hs, mem_range.2 hj⟩, mem_filter.2 ⟨mem_univ _, hmem⟩⟩
    have hcnt : A'.card * ((M : ℝ) + 1) / 2 < cnt A' M (c j) ((s : ZMod q) * r) := by
      by_contra hcon
      exact hnb (mem_filter.2 ⟨mem_univ _, not_lt.1 hcon⟩)
    obtain ⟨a', ha', v, hv, hv2⟩ := hit_of_cnt A' M (c j) _ hcnt
    obtain ⟨a, ha, rfl⟩ := mem_image.1 ha'
    refine ⟨a, ha, ?_⟩
    -- `|v| ≤ ρ`
    have hvρ : v.natAbs ≤ ρ := by
      rw [hρ, Nat.le_div_iff_mul_le hBpos]
      have hMJ : ((M : ℤ) + 1) = (J : ℤ) ^ 2 := by exact_mod_cast hM1
      rw [hMJ] at hv2
      have hJB' : (J : ℤ) = 2 * B := by exact_mod_cast hJB
      have h3 : ((v.natAbs : ℤ) * B) ^ 2 < (q : ℤ) ^ 2 := by
        have h4 : ((v.natAbs : ℤ) * B) ^ 2 = v ^ 2 * (B : ℤ) ^ 2 := by
          rw [mul_pow, Int.natCast_natAbs, sq_abs]
        have h5 : (0 : ℤ) ≤ v ^ 2 * (B : ℤ) ^ 2 := by positivity
        rw [h4]
        have h6 : 2 * (J : ℤ) ^ 2 * v ^ 2 = 8 * (v ^ 2 * (B : ℤ) ^ 2) := by rw [hJB']; ring
        linarith
      have h7 : (v.natAbs : ℤ) * B < q :=
        lt_of_pow_lt_pow_left₀ 2 (Int.natCast_nonneg q) h3
      have h8 : v.natAbs * B < q := by exact_mod_cast h7
      exact h8.le
    have hvabs : |v| ≤ ρ := by rw [Int.abs_eq_natAbs]; exact_mod_cast hvρ
    have hval : ((s : ZMod q) * r * (a : ZMod q)).valMinAbs = v + 2 ^ j * g := by
      rw [ZMod.valMinAbs_spec]
      have hρg' : (ρ : ℤ) < g := by exact_mod_cast hρg
      have hp1 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have hg0 : (0 : ℤ) ≤ g := Int.natCast_nonneg g
      have h7 : (1 : ℤ) * g ≤ 2 ^ j * g := mul_le_mul_of_nonneg_right hp1 hg0
      have hpj : (2 : ℤ) * 2 ^ j ≤ 2 ^ m := by
        rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hj
      have h8 : (2 : ℤ) * 2 ^ j * g ≤ 2 ^ m * g := mul_le_mul_of_nonneg_right hpj hg0
      have hpm : (2 : ℤ) ≤ 2 ^ m := by
        calc (2 : ℤ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
      have h9 : (2 : ℤ) * g ≤ 2 ^ m * g := mul_le_mul_of_nonneg_right hpm hg0
      have h10 : ((g * 2 ^ (m + 1) : ℕ) : ℤ) ≤ q := by exact_mod_cast hg2
      push_cast at h10
      rw [pow_succ] at h10
      have hq0' : (0 : ℤ) < q := by exact_mod_cast hqp.pos
      rw [abs_le] at hvabs
      refine ⟨?_, ?_, ?_⟩
      · have : ((s : ZMod q) * r * (a : ZMod q)) = (v : ZMod q) + c j := by rw [hv]; ring
        rw [this, hc]; push_cast; ring
      · linarith
      · linarith
    rw [hval, add_sub_cancel_right]
    exact hvabs
  -- Dirichlet and pigeonhole
  have hdir : ∀ x : ℤ, ∃ s, s ∈ Icc 1 J ∧ ∃ v : ℤ,
      (v : ZMod q) = (s : ZMod q) * (r * (x : ZMod q)) ∧ |v| < ρ := fun x ↦
    dirichlet ρ J hwJ (r * (x : ZMod q))
  choose sA hsA hsAv using hdir
  obtain ⟨s, hs, hcard⟩ : ∃ s ∈ Icc 1 J, A.card / J ≤ (A.filter fun x ↦ sA x = s).card := by
    refine exists_le_card_fiber_of_mul_le_card_of_maps_to (fun x _ ↦ hsA x) ?_ ?_
    · exact ⟨1, mem_Icc.2 ⟨le_rfl, hJpos⟩⟩
    · rw [Nat.card_Icc, Nat.add_sub_cancel]; exact Nat.mul_div_le _ _
  set A₁ := A.filter fun x ↦ sA x = s with hA₁
  have hnear : ∀ d ∈ A₁, |((s : ZMod q) * r * (d : ZMod q)).valMinAbs| ≤ ρ := by
    intro d hd
    obtain ⟨v, hv, hvlt⟩ := hsAv d
    rw [(mem_filter.1 hd).2] at hv
    have hval : ((s : ZMod q) * r * (d : ZMod q)).valMinAbs = v := by
      rw [ZMod.valMinAbs_spec]
      rw [abs_lt] at hvlt
      have h3 : ((2 * ρ : ℕ) : ℤ) ≤ q := by exact_mod_cast h2ρq
      push_cast at h3
      refine ⟨by rw [hv]; ring, ?_, ?_⟩ <;> linarith
    rw [hval]; exact hvlt.le
  have hitss := hits s hs
  choose! a haA ha using hitss
  set E := (range m).image a with hE
  have hinj : Set.InjOn a (range m) :=
    (lift ((s : ZMod q) * r) g ρ m K h1 hg2 a ∅ (by simp) (by simp) (by simp) ha).1
  refine ⟨A₁, filter_subset _ _, hcard, E, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
    exact haA j (mem_range.1 hj)
  · rw [hE, card_image_of_injOn hinj, card_range]
  · intro D hD hDdiss hDK
    obtain ⟨-, hnot, hdiss⟩ := lift ((s : ZMod q) * r) g ρ m K h1 hg2 a D hDdiss hDK
      (fun d hd ↦ hnear d (hD hd)) ha
    refine ⟨?_, hdiss⟩
    rw [disjoint_left]
    intro x hxD hxE
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hxE
    exact hnot j (mem_range.1 hj) hxD

end Erdos963
