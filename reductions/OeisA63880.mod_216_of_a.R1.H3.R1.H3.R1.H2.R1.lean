import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H3_R1_H3_R1

-- Reduction OeisA63880.mod_216_of_a.R1.H3.R1.H3.R1.H2.R1 of step
-- OeisA63880.mod_216_of_a.R1.H3.R1.H3.R1.H2
-- Credit: @Ciphore
-- Proves the budget exclusions `25 ∤ t`, `49 ∤ t`, `1331 ∤ t` for solutions of
-- the transformed equation and narrows the residual sieve by the divisibility
-- of `11^2`.

namespace OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H3_R1_H2_R1

open OeisA63880
open scoped ArithmeticFunction.sigma

private theorem splitUnitary {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) :
    unitaryDivisors (m*q) = unitaryDivisors m ∪ (unitaryDivisors m).image (· * q) := by
  have hq0 := hq.pos
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨t, ht⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_mul_pos_right (ht ▸ Nat.mul_pos hm hq0)
    rw [ht, Nat.mul_div_cancel_left _ hd0] at hcd
    have hqt : q ∣ d*t := ht ▸ dvd_mul_left q m
    rcases (hcd.isPrimePow_dvd_mul hq).1 hqt with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have he : m = b*t := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      have hb : 0 < b := Nat.pos_of_mul_pos_left hd0
      exact Or.inr ⟨b, ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hb] using (Nat.coprime_mul_iff_left.1 hcd).2⟩, mul_comm ..⟩
    · have he : m = d*b := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      exact Or.inl ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hd0] using (Nat.coprime_mul_iff_right.1 hcd).2⟩
  · rintro (⟨⟨⟨t, rfl⟩, -⟩, hcd⟩ | ⟨b, ⟨⟨⟨t, rfl⟩, -⟩, hcd⟩, rfl⟩)
    · have hd := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) q, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd]
      exact hcd.mul_right (Nat.coprime_mul_iff_right.1 hc).1.symm
    · have hb := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hb] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right b t) dvd_rfl, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_right_comm b t q, Nat.mul_div_cancel_left _ (Nat.mul_pos hb hq0)]
      exact hcd.mul_left (Nat.coprime_mul_iff_right.1 hc).2

private theorem unitarySum {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) : usigma (m*q) = usigma m * (q+1) := by
  have dis : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * q)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hd'
    have dvd : b*q ∣ m := (Nat.mem_divisors.1 (Finset.mem_filter.1 hd).1).1
    exact hq.ne_one (hc.eq_one_of_dvd ((dvd_mul_left q b).trans dvd))
  unfold usigma
  rw [splitUnitary hm hq hc, Finset.sum_union dis,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hq.pos h),
    ← Finset.sum_mul, mul_add, mul_one, add_comm]

theorem usigma_le_sigma (t : ℕ) : usigma t ≤ σ 1 t := by
  unfold usigma
  rw [ArithmeticFunction.sigma_one_apply]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    exact (Finset.mem_filter.1 hx).1
  · intro x _ _
    exact Nat.zero_le x

theorem usigma_pos {t : ℕ} (ht : 0 < t) : 0 < usigma t := by
  unfold usigma
  have h1 : 1 ∈ unitaryDivisors t := by
    rw [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd t, ht.ne'⟩, Nat.coprime_one_left _⟩
  exact Finset.single_le_sum (fun i _ => Nat.zero_le i) h1

/-- Exact prime-power extraction: if `p^2 ∣ t`, write `t = p^a * u` with
`a = t.factorization p`, `2 ≤ a`, and `¬ p ∣ u`. -/
theorem exact_power_extraction {t p : ℕ} (ht : 0 < t) (hp : p.Prime) (hdiv : p ^ 2 ∣ t) :
    ∃ a u : ℕ, t = p ^ a * u ∧ 2 ≤ a ∧ ¬ p ∣ u ∧ 0 < u := by
  have ht0 : t ≠ 0 := ht.ne'
  have a_def : t.factorization p ≥ 2 := (hp.pow_dvd_iff_le_factorization ht0).1 hdiv
  set a := t.factorization p with ha
  have hpa : p ^ a ∣ t := (hp.pow_dvd_iff_le_factorization ht0).2 (le_refl a)
  refine ⟨a, t / p ^ a, (Nat.mul_div_cancel' hpa).symm, a_def, ?_, ?_⟩
  · intro hpu
    obtain ⟨s, hs⟩ := hpu
    have hpp1 : p ^ (a + 1) ∣ t := by
      use s
      have hm : t = p ^ a * (t / p ^ a) := (Nat.mul_div_cancel' hpa).symm
      rw [hm, hs]
      ring
    have hle := (hp.pow_dvd_iff_le_factorization ht0).1 hpp1
    omega
  · rcases Nat.eq_zero_or_pos (t / p ^ a) with hz | hp2
    · have hm : t = p ^ a * (t / p ^ a) := (Nat.mul_div_cancel' hpa).symm
      rw [hz, mul_zero] at hm
      exact absurd hm ht0
    · exact hp2

/-- The budget-exclusion template: if the local ratio at `p` already exceeds the
target `100/91` at exponent two, then `p^2` cannot divide a solution. -/
theorem budget_exclusion {t p : ℕ} (ht : 0 < t) (hp : p.Prime)
    (hr : 91 * σ 1 t = 100 * usigma t)
    (hbudget : ∀ a : ℕ, 2 ≤ a → 100 * (p ^ a + 1) < 91 * σ 1 (p ^ a)) :
    ¬ p ^ 2 ∣ t := by
  intro hdiv
  obtain ⟨a, u, htu, ha2, hpu, hu0⟩ := exact_power_extraction ht hp hdiv
  have ht0 : t ≠ 0 := ht.ne'
  have hpos_a : 0 < a := by omega
  have hcop_pu : Nat.Coprime p u := (hp.coprime_iff_not_dvd).2 hpu
  have hcop : Nat.Coprime (p ^ a) u := by
    exact (Nat.coprime_pow_left_iff hpos_a p u).2 hcop_pu
  have hpp : IsPrimePow (p ^ a) := (isPrimePow_nat_iff _).2 ⟨p, a, hp, hpos_a, rfl⟩
  -- transform both arithmetic functions
  have hsg : σ 1 t = σ 1 (p ^ a) * σ 1 u := by
    rw [htu]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have hug : usigma t = usigma u * (p ^ a + 1) := by
    have hcomm : t = u * p ^ a := by rw [htu, mul_comm]
    rw [hcomm]
    exact unitarySum hu0 hpp hcop
  rw [hsg, hug] at hr
  -- inequality chain
  have hule := usigma_le_sigma u
  have hupos := usigma_pos hu0
  have hr2 : 91 * σ 1 (p ^ a) * σ 1 u = 100 * (p ^ a + 1) * usigma u := by
    linear_combination hr
  have chain : 91 * σ 1 (p ^ a) * usigma u ≤ 100 * (p ^ a + 1) * usigma u := by
    calc 91 * σ 1 (p ^ a) * usigma u
        ≤ 91 * σ 1 (p ^ a) * σ 1 u := Nat.mul_le_mul_left _ hule
      _ = 100 * (p ^ a + 1) * usigma u := hr2
  have cancel : 91 * σ 1 (p ^ a) ≤ 100 * (p ^ a + 1) := by
    exact Nat.le_of_mul_le_mul_right chain hupos
  have contra := hbudget a ha2
  omega

/-- Budget at the prime `5`: already exceeded at exponent two. -/
theorem budget_five_geom : ∀ a : ℕ, 2 ≤ a →
    100 * (5 ^ a + 1) < 91 * ∑ i ∈ Finset.range (a + 1), 5 ^ i := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => norm_num [Finset.sum_range_succ]
  | succ k hk ih =>
    rw [Finset.sum_range_succ]
    have h51 : (5 : ℕ) ^ (k + 1) = 5 * 5 ^ k := by ring
    rw [h51]
    omega

theorem budget_five : ∀ a : ℕ, 2 ≤ a → 100 * (5 ^ a + 1) < 91 * σ 1 (5 ^ a) := by
  intro a ha
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_five]
  exact budget_five_geom a ha

theorem not_twentyfive_dvd {t : ℕ} (ht : 0 < t)
    (hr : 91 * σ 1 t = 100 * usigma t) : ¬ 25 ∣ t := by
  have h : (25 : ℕ) = 5 ^ 2 := by norm_num
  rw [h]
  exact budget_exclusion ht Nat.prime_five hr budget_five

/-- Budget at the prime `7`. -/
theorem budget_seven_geom : ∀ a : ℕ, 2 ≤ a →
    100 * (7 ^ a + 1) < 91 * ∑ i ∈ Finset.range (a + 1), 7 ^ i := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => norm_num [Finset.sum_range_succ]
  | succ k hk ih =>
    rw [Finset.sum_range_succ]
    have h71 : (7 : ℕ) ^ (k + 1) = 7 * 7 ^ k := by ring
    rw [h71]
    omega

theorem budget_seven : ∀ a : ℕ, 2 ≤ a → 100 * (7 ^ a + 1) < 91 * σ 1 (7 ^ a) := by
  intro a ha
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (Nat.prime_seven)]
  exact budget_seven_geom a ha

theorem not_fortynine_dvd {t : ℕ} (ht : 0 < t)
    (hr : 91 * σ 1 t = 100 * usigma t) : ¬ 49 ∣ t := by
  have h : (49 : ℕ) = 7 ^ 2 := by norm_num
  rw [h]
  exact budget_exclusion ht (Nat.prime_seven) hr budget_seven

/-- The budget-exclusion template at exponent three. -/
theorem budget_exclusion_three {t p : ℕ} (ht : 0 < t) (hp : p.Prime)
    (hr : 91 * σ 1 t = 100 * usigma t)
    (hbudget : ∀ a : ℕ, 3 ≤ a → 100 * (p ^ a + 1) < 91 * σ 1 (p ^ a)) :
    ¬ p ^ 3 ∣ t := by
  intro hdiv
  have ht0 : t ≠ 0 := ht.ne'
  have a_def : t.factorization p ≥ 3 := (hp.pow_dvd_iff_le_factorization ht0).1 hdiv
  set a := t.factorization p with ha
  have hpa : p ^ a ∣ t := (hp.pow_dvd_iff_le_factorization ht0).2 (le_refl a)
  have hnotpu : ¬ p ∣ (t / p ^ a) := by
    intro hpu
    obtain ⟨s, hs⟩ := hpu
    have hpp1 : p ^ (a + 1) ∣ t := by
      use s
      have hm : t = p ^ a * (t / p ^ a) := (Nat.mul_div_cancel' hpa).symm
      rw [hm, hs]
      ring
    have hle := (hp.pow_dvd_iff_le_factorization ht0).1 hpp1
    omega
  have hu0 : 0 < t / p ^ a := by
    rcases Nat.eq_zero_or_pos (t / p ^ a) with hz | hp2
    · have hm : t = p ^ a * (t / p ^ a) := (Nat.mul_div_cancel' hpa).symm
      rw [hz, mul_zero] at hm
      exact absurd hm ht0
    · exact hp2
  set u := t / p ^ a with hu
  have htu : t = p ^ a * u := (Nat.mul_div_cancel' hpa).symm
  have hpos_a : 0 < a := by omega
  have ha3 : 3 ≤ a := a_def
  have hcop_pu : Nat.Coprime p u := (hp.coprime_iff_not_dvd).2 hnotpu
  have hcop : Nat.Coprime (p ^ a) u := (Nat.coprime_pow_left_iff hpos_a p u).2 hcop_pu
  have hpp : IsPrimePow (p ^ a) := (isPrimePow_nat_iff _).2 ⟨p, a, hp, hpos_a, rfl⟩
  have hsg : σ 1 t = σ 1 (p ^ a) * σ 1 u := by
    rw [htu]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have hug : usigma t = usigma u * (p ^ a + 1) := by
    have hcomm : t = u * p ^ a := by rw [htu, mul_comm]
    rw [hcomm]
    exact unitarySum hu0 hpp hcop
  rw [hsg, hug] at hr
  have hule := usigma_le_sigma u
  have hupos := usigma_pos hu0
  have hr2 : 91 * σ 1 (p ^ a) * σ 1 u = 100 * (p ^ a + 1) * usigma u := by
    linear_combination hr
  have chain : 91 * σ 1 (p ^ a) * usigma u ≤ 100 * (p ^ a + 1) * usigma u := by
    calc 91 * σ 1 (p ^ a) * usigma u
        ≤ 91 * σ 1 (p ^ a) * σ 1 u := Nat.mul_le_mul_left _ hule
      _ = 100 * (p ^ a + 1) * usigma u := hr2
  have cancel : 91 * σ 1 (p ^ a) ≤ 100 * (p ^ a + 1) :=
    Nat.le_of_mul_le_mul_right chain hupos
  have contra := hbudget a ha3
  omega

/-- The budget at `11` already fails at exponent three:
`91 * 1464 = 133224 > 133200 = 100 * 1332`. -/
theorem budget_eleven_geom : ∀ a : ℕ, 3 ≤ a →
    100 * (11 ^ a + 1) < 91 * ∑ i ∈ Finset.range (a + 1), 11 ^ i := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => norm_num [Finset.sum_range_succ]
  | succ k hk ih =>
    rw [Finset.sum_range_succ]
    have h111 : (11 : ℕ) ^ (k + 1) = 11 * 11 ^ k := by ring
    rw [h111]
    omega

theorem budget_eleven : ∀ a : ℕ, 3 ≤ a → 100 * (11 ^ a + 1) < 91 * σ 1 (11 ^ a) := by
  intro a ha
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (show Nat.Prime 11 by norm_num)]
  exact budget_eleven_geom a ha

theorem not_eleven_cubed_dvd {t : ℕ} (ht : 0 < t)
    (hr : 91 * σ 1 t = 100 * usigma t) : ¬ 1331 ∣ t := by
  have h : (1331 : ℕ) = 11 ^ 3 := by norm_num
  rw [h]
  exact budget_exclusion_three ht (show Nat.Prime 11 by norm_num) hr budget_eleven


/-- The residual sieve core with a repeated factor of `11^2`. -/
def H1 : Prop := ∀ t : ℕ, Odd t → ¬ 3 ∣ t → ¬ Squarefree t → ¬ IsPrimePow t →
  ¬ 25 ∣ t → ¬ 49 ∣ t → ¬ 1331 ∣ t → (11:ℕ) ^ 2 ∣ t →
  91 * σ 1 t ≠ 100 * usigma t

/-- The residual sieve core whose repeated primes are all at least `13`. -/
def H2 : Prop := ∀ t : ℕ, Odd t → ¬ 3 ∣ t → ¬ Squarefree t → ¬ IsPrimePow t →
  ¬ 25 ∣ t → ¬ 49 ∣ t → ¬ 1331 ∣ t → ¬ (11:ℕ) ^ 2 ∣ t →
  91 * σ 1 t ≠ 100 * usigma t

theorem main : H1 → H2 → OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H3_R1.H2 := by
  intro h1 h2 t htodd ht3 hnsq hnp hr
  have ht : 0 < t := by
    obtain ⟨k, hk⟩ := htodd
    omega
  have h25 := not_twentyfive_dvd ht hr
  have h49 := not_fortynine_dvd ht hr
  have h1331 := not_eleven_cubed_dvd ht hr
  by_cases h11 : (11:ℕ) ^ 2 ∣ t
  · exact h1 t htodd ht3 hnsq hnp h25 h49 h1331 h11 hr
  · exact h2 t htodd ht3 hnsq hnp h25 h49 h1331 h11 hr

end OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H3_R1_H2_R1
