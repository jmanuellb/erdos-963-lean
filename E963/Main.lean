module

public import E963.Upper

/-!
# Erdős 963, part i: `f n ~ log₂ n`

The main result of this file is `f_isEquivalent_logb`. The theorem `erdos_963.parts.i`, with the
statement of `FormalConjectures/ErdosProblems/963.lean` and the answer `n ↦ Real.logb 2 n`, is
derived from it in `Solution.lean`.
-/

@[expose] public section

open Filter Asymptotics Finset

namespace Erdos963

/-- Exponentials beat polynomials. -/
lemma exists_pow_le_two_pow (k C : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, (C * m) ^ k ≤ 2 ^ m := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
  have hε : (0 : ℝ) < 1 / ((C : ℝ) ^ k + 1) := by positivity
  have hev : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ k / 2 ^ m < 1 / ((C : ℝ) ^ k + 1) :=
    h.eventually (gt_mem_nhds hε)
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 hev
  refine ⟨m₀, fun m hm ↦ ?_⟩
  have h1 := hm₀ m hm
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity)] at h1
  have h3 : ((C : ℝ) * m) ^ k ≤ 2 ^ m := by
    rw [mul_pow]
    have h4 : (0 : ℝ) ≤ (m : ℝ) ^ k := by positivity
    nlinarith
  exact_mod_cast h3

/-- Clean form of the lower bound: `f n ≥ t m` as soon as `n ≥ 2 ^ (m (t + 7))` and `m` is
large in terms of `t`. -/
lemma f_lower' (t : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ n, 2 ^ (m * (t + 7)) ≤ n → t * m ≤ f n := by
  obtain ⟨m₁, hm₁⟩ := exists_pow_le_two_pow (t + 6) (16 * (t + 1))
  refine ⟨m₁ + 1, fun m hm n hn ↦ ?_⟩
  have hm1 : 1 ≤ m := by omega
  refine f_lower m t n hm1 (le_trans ?_ hn)
  obtain ⟨J, hJ⟩ : ∃ J, J = 2 ^ (m + 4) * (m + t * m) := ⟨_, rfl⟩
  rw [← hJ]
  have hJeq : J = 2 ^ m * (16 * (t + 1) * m) := by rw [hJ, pow_add]; ring
  have hJ4 : 4 * m + 1 ≤ J := by
    rw [hJeq]
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    calc 4 * m + 1 ≤ 1 * (16 * (t + 1) * m) := by nlinarith [Nat.zero_le (t * m)]
      _ ≤ 2 ^ m * (16 * (t + 1) * m) := Nat.mul_le_mul_right _ h1
  calc (4 * m * J ^ 5 + 1) * J ^ t ≤ (J * J ^ 5) * J ^ t := by
        refine Nat.mul_le_mul_right _ ?_
        have h5 : 1 ≤ J ^ 5 := Nat.one_le_pow _ _ (by omega)
        have h6 := Nat.mul_le_mul_right (J ^ 5) hJ4
        nlinarith
    _ = J ^ (t + 6) := by ring
    _ = (2 ^ m) ^ (t + 6) * (16 * (t + 1) * m) ^ (t + 6) := by rw [hJeq, mul_pow]
    _ ≤ (2 ^ m) ^ (t + 6) * 2 ^ m := Nat.mul_le_mul_left _ (hm₁ m (by omega))
    _ = 2 ^ (m * (t + 7)) := by
        rw [← pow_mul, ← pow_add]; congr 1

lemma tendsto_logb_nat : Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ)) atTop atTop :=
  (Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop

lemma upper_ev (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) - Real.logb 2 n ≤ c * Real.logb 2 n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key : ∀ᶠ x : ℝ in atTop, Real.logb 2 (2 + 2 * x) ≤ c * x := by
    have hε : 0 < c * Real.log 2 / 4 := by positivity
    have hlo := Real.isLittleO_log_id_atTop.def hε
    have htend : Tendsto (fun x : ℝ ↦ 2 + 2 * x) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (by norm_num))
    filter_upwards [htend.eventually hlo, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hpos : (0 : ℝ) < 2 + 2 * x := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hpos] at hx
    have h1 : Real.log (2 + 2 * x) ≤ c * Real.log 2 / 4 * (2 + 2 * x) := (le_abs_self _).trans hx
    rw [Real.logb, div_le_iff₀ hl2]
    have h2 : 0 ≤ c * Real.log 2 * (x - 1) :=
      mul_nonneg (mul_nonneg hc.le hl2.le) (by linarith)
    nlinarith
  filter_upwards [tendsto_logb_nat.eventually key, eventually_ge_atTop 1] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  set x := Real.logb 2 (n : ℝ) with hx
  have hx0 : 0 ≤ x := Real.logb_nonneg one_lt_two hnR
  set L := Nat.log 2 (n * n + 1) with hL
  -- bound on `L`
  have hL1 : (L : ℝ) ≤ 1 + 2 * x := by
    have h1 : (L : ℝ) ≤ Real.logb 2 ((n * n + 1 : ℕ) : ℝ) := by
      have := Real.natLog_le_logb (n * n + 1) 2
      simpa using this
    have h2 : Real.logb 2 ((n * n + 1 : ℕ) : ℝ) ≤ Real.logb 2 (2 * n * n) := by
      refine Real.logb_le_logb_of_le one_lt_two (by positivity) ?_
      push_cast
      nlinarith
    have h3 : Real.logb 2 (2 * (n : ℝ) * n) = 1 + 2 * x := by
      rw [Real.logb_mul (by positivity) hn0.ne', Real.logb_mul (by norm_num) hn0.ne',
        Real.logb_self_eq_one one_lt_two]
      ring
    linarith
  have hf : (f n : ℝ) ≤ Real.logb 2 ((L * n + 1 : ℕ) : ℝ) := by
    have h1 : ((f n : ℕ) : ℝ) ≤ (Nat.log 2 (L * n + 1) : ℝ) := by exact_mod_cast f_upper n
    have h2 := Real.natLog_le_logb (L * n + 1) 2
    have h3 : (Nat.log 2 (L * n + 1) : ℝ) ≤ Real.logb 2 ((L * n + 1 : ℕ) : ℝ) := by
      simpa using h2
    linarith
  have h4 : Real.logb 2 ((L * n + 1 : ℕ) : ℝ) ≤ Real.logb 2 (((L : ℝ) + 1) * n) := by
    refine Real.logb_le_logb_of_le one_lt_two (by positivity) ?_
    push_cast
    nlinarith
  have h5 : Real.logb 2 (((L : ℝ) + 1) * n) = Real.logb 2 ((L : ℝ) + 1) + x := by
    rw [Real.logb_mul (by positivity) hn0.ne']
  have h6 : Real.logb 2 ((L : ℝ) + 1) ≤ Real.logb 2 (2 + 2 * x) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  linarith

lemma lower_ev (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.logb 2 n - (f n : ℝ) ≤ c * Real.logb 2 n := by
  set t : ℕ := ⌈14 / c⌉₊ with ht
  have htc : 14 / c ≤ t := Nat.le_ceil _
  have htc' : 14 ≤ c * t := by
    rw [div_le_iff₀ hc] at htc; linarith
  obtain ⟨m₀, hm₀⟩ := f_lower' t
  filter_upwards [tendsto_logb_nat.eventually
    (eventually_ge_atTop (((m₀ : ℝ) + 1) * (t + 7) + 1 + 2 * (t + 1) / c)),
    eventually_ge_atTop 1] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  set x := Real.logb 2 (n : ℝ) with hx
  have ht7 : (0 : ℝ) < (t : ℝ) + 7 := by positivity
  have hm0nn : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg _
  have htnn : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hdivnn : 0 ≤ 2 * ((t : ℝ) + 1) / c := by positivity
  have hprod : (0 : ℝ) ≤ (m₀ : ℝ) * (t + 7) := by positivity
  have hx1 : ((m₀ : ℝ) + 1) * (t + 7) + 1 ≤ x := by linarith
  have hx2 : 2 * ((t : ℝ) + 1) ≤ c * x := by
    have h1 : 2 * ((t : ℝ) + 1) / c ≤ x := by nlinarith
    rw [div_le_iff₀ hc] at h1; linarith
  set d := (x - 1) / ((t : ℝ) + 7) with hd
  have hdmul : d * ((t : ℝ) + 7) = x - 1 := div_mul_cancel₀ _ ht7.ne'
  have hd0 : (m₀ : ℝ) ≤ d := by
    rw [hd, le_div_iff₀ ht7]; nlinarith
  have hdnn : 0 ≤ d := hm0nn.trans hd0
  set m := ⌊d⌋₊ with hm
  have hmm₀ : m₀ ≤ m := Nat.le_floor hd0
  have hmle : (m : ℝ) ≤ d := Nat.floor_le hdnn
  have hmgt : d < (m : ℝ) + 1 := Nat.lt_floor_add_one d
  have hpow : 2 ^ (m * (t + 7)) ≤ n := by
    have h1 : ((2 : ℝ)) ^ (m * (t + 7)) ≤ n := by
      rw [← Real.rpow_natCast]
      have h2 : ((m * (t + 7) : ℕ) : ℝ) ≤ x := by
        push_cast
        have := mul_le_mul_of_nonneg_right hmle ht7.le
        linarith
      calc (2 : ℝ) ^ ((m * (t + 7) : ℕ) : ℝ) ≤ (2 : ℝ) ^ x :=
            Real.rpow_le_rpow_of_exponent_le one_le_two h2
        _ = n := Real.rpow_logb two_pos (by norm_num) hn0
    exact_mod_cast h1
  have hf : ((t * m : ℕ) : ℝ) ≤ (f n : ℝ) := by exact_mod_cast hm₀ m hmm₀ n hpow
  push_cast at hf
  have h1 : (t : ℝ) * (d - 1) ≤ t * m := mul_le_mul_of_nonneg_left (by linarith) htnn
  have h2 : 14 * d ≤ c * x := by
    have h3 : 14 * d ≤ c * ((t : ℝ) + 7) * d :=
      mul_le_mul_of_nonneg_right (by nlinarith) hdnn
    have h4 : c * ((t : ℝ) + 7) * d = c * (x - 1) := by rw [mul_assoc, mul_comm _ d, hdmul]
    nlinarith
  have h5 : (t : ℝ) * d = x - 1 - 7 * d := by linarith
  nlinarith

/--
Let $f(n)$ be the maximal $k$ such that in any set $A\subset \mathbb{R}$ of size $n$ there is a
subset $B\subseteq A$ of size $\lvert B\rvert\geq k$ which is dissociated, that is, the sums
$\sum_{b\in S}b$ are distinct for all $S\subseteq B$. Then $f(n)\sim\log_2 n$.

This is the first part of Erdős problem 963 with the answer written out.
-/
theorem f_isEquivalent_logb :
    (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] fun n : ℕ ↦ Real.logb 2 n := by
  rw [Asymptotics.IsEquivalent, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [upper_ev c hc, lower_ev c hc, eventually_ge_atTop 1] with n h1 h2 hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg one_lt_two hnR
  simp only [Pi.sub_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx, abs_le]
  constructor <;> linarith

end Erdos963
