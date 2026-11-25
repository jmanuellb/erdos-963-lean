module

public import E963.Defs

/-!
# Erdős 963 — the Fejér-type kernel on `ZMod q` and the second moment bound
-/

@[expose] public section

open Finset

namespace Erdos963

variable {q : ℕ} [NeZero q]

local notation "χ" => (ZMod.stdAddChar (N := q))

lemma norm_chi (x : ZMod q) : ‖χ x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

/-- Lower bound for the chord `‖χ x - 1‖`. -/
lemma chi_sub_one_lower (x : ZMod q) :
    4 * |(x.valMinAbs : ℝ)| / q ≤ ‖χ x - 1‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  set v : ℤ := x.valMinAbs with hv
  have hx : χ x = Complex.exp (Complex.I * ((2 * Real.pi * v / q : ℝ) : ℂ)) := by
    conv_lhs => rw [← ZMod.coe_valMinAbs x]
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [hx, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hmem := ZMod.valMinAbs_mem_Ioc x
  have h1 : -(q : ℝ) < (v : ℝ) * 2 := by exact_mod_cast hmem.1
  have h2 : (v : ℝ) * 2 ≤ q := by exact_mod_cast hmem.2
  set y : ℝ := 2 * Real.pi * v / q / 2 with hy
  have hy' : y = Real.pi * v / q := by rw [hy]; ring
  have hpi := Real.pi_pos
  have habs : |y| ≤ Real.pi / 2 := by
    rw [hy', abs_le]
    constructor
    · rw [le_div_iff₀ hq]; nlinarith
    · rw [div_le_iff₀ hq]; nlinarith
  have hsin : 2 / Real.pi * |y| ≤ |Real.sin y| := by
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h] at habs ⊢
      exact (Real.mul_le_sin h habs).trans (le_abs_self _)
    · rw [abs_of_nonpos h] at habs ⊢
      have := Real.mul_le_sin (neg_nonneg.2 h) habs
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  have hyabs : |y| = Real.pi * |(v : ℝ)| / q := by
    rw [hy', abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hq]
  rw [Real.norm_eq_abs, abs_mul, abs_two]
  calc 4 * |(v : ℝ)| / q = 2 * (2 / Real.pi * |y|) := by
        rw [hyabs]; field_simp; ring
    _ ≤ 2 * |Real.sin y| := by linarith

/-- The Dirichlet-type sum `∑_{j ≤ M} χ(j x)`. -/
noncomputable def dir (M : ℕ) (x : ZMod q) : ℂ :=
  ∑ j ∈ range (M + 1), χ ((j : ZMod q) * x)

/-- The (unnormalised) Fejér kernel. -/
noncomputable def ker (M : ℕ) (x : ZMod q) : ℝ := ‖dir M x‖ ^ 2

lemma ker_nonneg (M : ℕ) (x : ZMod q) : 0 ≤ ker M x := sq_nonneg _

lemma dir_eq_geom (M : ℕ) (x : ZMod q) : dir M x = ∑ j ∈ range (M + 1), χ x ^ j := by
  unfold dir
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

lemma ker_le (M : ℕ) {x : ZMod q} (hx : x ≠ 0) :
    ker M x ≤ (q : ℝ) ^ 2 / (4 * (x.valMinAbs : ℝ) ^ 2) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hv : (x.valMinAbs : ℝ) ≠ 0 := by
    exact_mod_cast (not_iff_not.2 (ZMod.valMinAbs_eq_zero x)).2 hx
  have hvpos : 0 < |(x.valMinAbs : ℝ)| := abs_pos.2 hv
  have hlow := chi_sub_one_lower x
  have hpos : 0 < 4 * |(x.valMinAbs : ℝ)| / q := by positivity
  have hne : 0 < ‖χ x - 1‖ := lt_of_lt_of_le hpos hlow
  have hgeom : dir M x * (χ x - 1) = χ x ^ (M + 1) - 1 := by
    rw [dir_eq_geom, geom_sum_mul]
  have hnorm : ‖dir M x‖ * ‖χ x - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc ‖χ x ^ (M + 1) - 1‖ ≤ ‖χ x ^ (M + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_chi, one_pow, norm_one]; norm_num
  have hd : ‖dir M x‖ ≤ q / (2 * |(x.valMinAbs : ℝ)|) := by
    rw [le_div_iff₀ (by positivity)]
    have h3 : ‖dir M x‖ * (4 * |(x.valMinAbs : ℝ)| / q) ≤ 2 :=
      (mul_le_mul_of_nonneg_left hlow (norm_nonneg _)).trans hnorm
    have h4 : ‖dir M x‖ * (4 * |(x.valMinAbs : ℝ)| / q) * q
        = ‖dir M x‖ * (2 * |(x.valMinAbs : ℝ)|) * 2 := by
      field_simp; ring
    nlinarith
  unfold ker
  calc ‖dir M x‖ ^ 2 ≤ (q / (2 * |(x.valMinAbs : ℝ)|)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hd 2
    _ = (q : ℝ) ^ 2 / (4 * (x.valMinAbs : ℝ) ^ 2) := by
        rw [div_pow, mul_pow, sq_abs]; norm_num

lemma ker_cast (M : ℕ) (y : ZMod q) :
    ((ker M y : ℝ) : ℂ) =
      ∑ p ∈ range (M + 1) ×ˢ range (M + 1), χ (((p.1 : ZMod q) - (p.2 : ZMod q)) * y) := by
  unfold ker
  push_cast
  rw [← Complex.mul_conj', dir, map_sum, sum_mul_sum, ← sum_product']
  refine sum_congr rfl fun p _ ↦ ?_
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1; ring

variable (A : Finset (ZMod q))

/-- The exponential sum over `A`. -/
noncomputable def expSum (η : ZMod q) : ℂ := ∑ a ∈ A, χ (η * a)

/-- Weighted count of the `a ∈ A` with `r * a` close to `c`. -/
noncomputable def cnt (M : ℕ) (c r : ZMod q) : ℝ := ∑ a ∈ A, ker M (r * a - c)

lemma parseval : ∑ η : ZMod q, ‖expSum A η‖ ^ 2 = (q : ℝ) * A.card := by
  classical
  have h : ∀ η : ZMod q, ((‖expSum A η‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ A, ∑ b ∈ A, χ (η * (a - b)) := by
    intro η
    push_cast
    rw [← Complex.mul_conj', expSum, map_sum, sum_mul_sum]
    refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1; ring
  have h2 : ((∑ η : ZMod q, ‖expSum A η‖ ^ 2 : ℝ) : ℂ) = ((q : ℝ) * A.card : ℝ) := by
    rw [Complex.ofReal_sum]
    simp_rw [h]
    rw [sum_comm]
    simp_rw [sum_comm (s := (univ : Finset (ZMod q)))]
    simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), sub_eq_zero]
    simp [ZMod.card, mul_comm]
  exact_mod_cast h2

lemma cnt_sub (M : ℕ) (c r : ZMod q) :
    ((cnt A M c r : ℝ) : ℂ) - (A.card : ℂ) * (M + 1) =
      ∑ p ∈ (range (M + 1)).offDiag,
        χ (-(((p.1 : ZMod q) - (p.2 : ZMod q)) * c)) *
          expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r) := by
  classical
  unfold cnt
  rw [Complex.ofReal_sum]
  simp_rw [ker_cast]
  rw [sum_comm, ← diag_union_offDiag, sum_union (disjoint_diag_offDiag _), sum_diag]
  have h1 : ∑ i ∈ range (M + 1), ∑ a ∈ A, χ (((i : ZMod q) - (i : ZMod q)) * (r * a - c))
      = (A.card : ℂ) * (M + 1) := by
    simp [mul_comm]
  rw [h1, add_sub_cancel_left]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [expSum, mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [← AddChar.map_add_eq_mul]
  congr 1; ring

lemma second_moment (M : ℕ) (hM : M + 1 ≤ q) [Fact q.Prime] (c : ZMod q) :
    ∑ r : ZMod q, (cnt A M c r - A.card * (M + 1)) ^ 2 ≤
      ((M : ℝ) + 1) ^ 4 * q * A.card := by
  classical
  set P := (range (M + 1)).offDiag with hP
  have hPcard : (P.card : ℝ) ≤ ((M : ℝ) + 1) ^ 2 := by
    have : P.card ≤ (M + 1) * (M + 1) := by
      rw [hP, offDiag_card, card_range]; exact Nat.sub_le _ _
    calc (P.card : ℝ) ≤ ((M + 1) * (M + 1) : ℕ) := by exact_mod_cast this
      _ = ((M : ℝ) + 1) ^ 2 := by push_cast; ring
  have hpt : ∀ r : ZMod q, (cnt A M c r - A.card * (M + 1)) ^ 2 ≤
      P.card * ∑ p ∈ P, ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖ ^ 2 := by
    intro r
    have h1 : |cnt A M c r - A.card * (M + 1)| ≤
        ∑ p ∈ P, ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖ := by
      have : ((cnt A M c r - A.card * (M + 1) : ℝ) : ℂ) =
          ((cnt A M c r : ℝ) : ℂ) - (A.card : ℂ) * (M + 1) := by push_cast; ring
      rw [← Real.norm_eq_abs, ← Complex.norm_real, this, cnt_sub]
      refine (norm_sum_le _ _).trans (sum_le_sum fun p _ ↦ ?_)
      rw [norm_mul, norm_chi, one_mul]
    calc (cnt A M c r - A.card * (M + 1)) ^ 2
        = |cnt A M c r - A.card * (M + 1)| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ p ∈ P, ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ _ := sq_sum_le_card_mul_sum_sq
  have hshift : ∀ p ∈ P, ∑ r : ZMod q,
      ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖ ^ 2 = (q : ℝ) * A.card := by
    intro p hp
    rw [hP, mem_offDiag] at hp
    have hd : ((p.1 : ZMod q) - (p.2 : ZMod q)) ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      rw [ZMod.natCast_eq_natCast_iff'] at h
      have h1 := mem_range.1 hp.1
      have h2 := mem_range.1 hp.2.1
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
      exact hp.2.2 h
    rw [← parseval A]
    exact Fintype.sum_equiv (Equiv.mulLeft₀ _ hd) _ _ fun r ↦ rfl
  calc ∑ r : ZMod q, (cnt A M c r - A.card * (M + 1)) ^ 2
      ≤ ∑ r : ZMod q, P.card *
          ∑ p ∈ P, ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖ ^ 2 :=
        sum_le_sum fun r _ ↦ hpt r
    _ = P.card * ∑ p ∈ P, ∑ r : ZMod q,
          ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖ ^ 2 := by
        rw [← mul_sum, sum_comm]
    _ = P.card * (P.card * ((q : ℝ) * A.card)) := by
        rw [sum_congr rfl hshift, sum_const, nsmul_eq_mul]
    _ ≤ ((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 1) ^ 2 * ((q : ℝ) * A.card)) := by
        gcongr
    _ = ((M : ℝ) + 1) ^ 4 * q * A.card := by ring

end Erdos963
