import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H3_R1

/-!
Two-repeated-prime collapse for the A063880 ratio equation: if `t = p^a * q^b * s`
with `a, b ≥ 2` and `s` squarefree coprime to both primes satisfies the ratio equation,
then `{p, q} = {5, 7}`.
-/

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

/-- For squarefree `s` every divisor is unitary. -/
theorem sqfree_unitaryDivisors {t : ℕ} (hsq : Squarefree t) :
    unitaryDivisors t = t.divisors := by
  ext d
  simp only [unitaryDivisors, Finset.mem_filter]
  constructor
  · intro h
    exact h.1
  · intro hd
    refine ⟨hd, ?_⟩
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, htpos⟩ := hd
    -- show coprime d (t/d): any common prime factor would square-divide t
    by_contra hnc
    have htpos' : t ≠ 0 := htpos
    have hd0 : d ≠ 0 := by
      intro hz
      rw [hz] at hdvd
      exact htpos' (Nat.eq_zero_of_zero_dvd hdvd)
    have hg1 : Nat.gcd d (t / d) ≠ 1 := hnc
    have hgpos : 0 < Nat.gcd d (t / d) := Nat.gcd_pos_of_pos_left (t / d) (Nat.pos_of_ne_zero hd0)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hg1
    have hd1 : p ∣ d := hpdvd.trans (Nat.gcd_dvd_left d (t / d))
    have hd2 : p ∣ t / d := hpdvd.trans (Nat.gcd_dvd_right d (t / d))
    have hsq2 : p * p ∣ t := by
      obtain ⟨a, ha⟩ := hd1
      obtain ⟨b, hb⟩ := hd2
      have htd : t = d * (t / d) := (Nat.mul_div_cancel' hdvd).symm
      rw [htd, hb, ha]
      use a * b
      ring
    have := hsq p hsq2
    exact hp.ne_one (Nat.isUnit_iff.1 this)

/-- For squarefree `s` the divisor sums agree. -/
theorem usigma_eq_sigma_of_squarefree {t : ℕ} (hsq : Squarefree t) :
    usigma t = σ 1 t := by
  unfold usigma
  rw [sqfree_unitaryDivisors hsq, ArithmeticFunction.sigma_one_apply]

/-- The geometric-sum identity in subtraction-free form. -/
theorem geom_sum_id (r e : ℕ) (hr : 1 ≤ r) :
    (r - 1) * (∑ i ∈ Finset.range (e + 1), r ^ i) + 1 = r ^ (e + 1) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ]
    have hexpand : r' * ((∑ i ∈ Finset.range (e + 1), (r' + 1) ^ i) + (r' + 1) ^ (e + 1)) + 1 =
        r' * (∑ i ∈ Finset.range (e + 1), (r' + 1) ^ i) + 1 + r' * (r' + 1) ^ (e + 1) := by
      ring
    rw [hexpand, ih]
    have hfin : (r' + 1) ^ (e + 1) + r' * (r' + 1) ^ (e + 1) = (r' + 1) ^ (e + 1 + 1) := by
      rw [pow_succ]
      ring
    exact hfin

/-- Strict ratio bound at a prime power. -/
theorem ratio_bound {r e : ℕ} (hr : r.Prime) :
    σ 1 (r ^ e) * (r - 1) < r * (r ^ e + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hr]
  have hr1 : 1 ≤ r := Nat.one_le_of_lt hr.pos
  have hid := geom_sum_id r e hr1
  calc (∑ i ∈ Finset.range (e + 1), r ^ i) * (r - 1)
      = (r - 1) * (∑ i ∈ Finset.range (e + 1), r ^ i) := by ring
    _ < (r - 1) * (∑ i ∈ Finset.range (e + 1), r ^ i) + 1 + r := by omega
    _ = r ^ (e + 1) + r := by rw [hid]
    _ = r * (r ^ e + 1) := by ring

/-- Sigma is positive at positive input. -/
theorem sigma_pos' (n : ℕ) (hn : n ≠ 0) : 0 < σ 1 n := ArithmeticFunction.sigma_pos 1 n hn

/-- The two-repeated-prime collapse: exactly two repeated primes in a solution
    must be `5` and `7`. -/
theorem two_prime_collapse {t p q a b s : ℕ}
    (ht : 0 < t) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hsq : Squarefree s) (hps : ¬ p ∣ s) (hqs : ¬ q ∣ s) (hs0 : 0 < s)
    (hteq : t = p ^ a * q ^ b * s)
    (heq : 7 * σ 1 t = 10 * usigma t) :
    (p = 5 ∧ q = 7) ∨ (p = 7 ∧ q = 5) := by
  have ht0 : t ≠ 0 := ht.ne'
  have hapos : 0 < a := by omega
  have hbpos : 0 < b := by omega
  have hpq_cop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hps_cop : Nat.Coprime p s := (hp.coprime_iff_not_dvd).2 hps
  have hqs_cop : Nat.Coprime q s := (hq.coprime_iff_not_dvd).2 hqs
  have hpa_qb : Nat.Coprime (p ^ a) (q ^ b) := hpq_cop.pow a b
  have hpa_s : Nat.Coprime (p ^ a) s := hps_cop.pow_left a
  have hqb_s : Nat.Coprime (q ^ b) s := hqs_cop.pow_left b
  have hpa_qbs : Nat.Coprime (p ^ a) (q ^ b * s) := hpa_qb.mul_right hpa_s
  have hppa : IsPrimePow (p ^ a) := (isPrimePow_nat_iff _).2 ⟨p, a, hp, hapos, rfl⟩
  have hppb : IsPrimePow (q ^ b) := (isPrimePow_nat_iff _).2 ⟨q, b, hq, hbpos, rfl⟩
  have hqbs0 : 0 < q ^ b * s := Nat.mul_pos (pow_pos hq.pos b) hs0
  have hug : usigma t = usigma s * (q ^ b + 1) * (p ^ a + 1) := by
    have hcomm : t = (q ^ b * s) * p ^ a := by rw [hteq]; ring
    rw [hcomm, unitarySum hqbs0 hppa hpa_qbs]
    have hcomm2 : q ^ b * s = s * q ^ b := mul_comm _ _
    rw [hcomm2, unitarySum hs0 hppb hqb_s]
  have hsg : σ 1 t = σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 s := by
    rw [hteq]
    have h1 : σ 1 (p ^ a * (q ^ b * s)) = σ 1 (p ^ a) * σ 1 (q ^ b * s) :=
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hpa_qbs
    have h2 : σ 1 (q ^ b * s) = σ 1 (q ^ b) * σ 1 s :=
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hqb_s
    calc σ 1 (p ^ a * q ^ b * s) = σ 1 (p ^ a * (q ^ b * s)) := by rw [mul_assoc]
      _ = σ 1 (p ^ a) * σ 1 (q ^ b * s) := h1
      _ = σ 1 (p ^ a) * (σ 1 (q ^ b) * σ 1 s) := by rw [h2]
      _ = σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 s := by ring
  have hsf : usigma s = σ 1 s := usigma_eq_sigma_of_squarefree hsq
  have hspos : 0 < σ 1 s := by
    have hu := usigma_pos hs0
    rwa [hsf] at hu
  rw [hsg, hug, hsf] at heq
  have hpure : 7 * (σ 1 (p ^ a) * σ 1 (q ^ b)) = 10 * ((p ^ a + 1) * (q ^ b + 1)) := by
    have heq2 : 7 * (σ 1 (p ^ a) * σ 1 (q ^ b)) * σ 1 s =
        10 * ((p ^ a + 1) * (q ^ b + 1)) * σ 1 s := by linear_combination heq
    exact Nat.eq_of_mul_eq_mul_right hspos heq2
  have hb1 := ratio_bound (e := a) hp
  have hb2 := ratio_bound (e := b) hq
  have hsp1 : 0 < σ 1 (p ^ a) * (p - 1) :=
    Nat.mul_pos (sigma_pos' _ (pow_pos hp.pos a).ne') (by omega)
  have hq1 : 0 < q * (q ^ b + 1) := Nat.mul_pos hq.pos (by omega)
  have key : (p - 1) * (q - 1) * (σ 1 (p ^ a) * σ 1 (q ^ b)) <
      p * q * ((p ^ a + 1) * (q ^ b + 1)) := by
    have h0 := mul_lt_mul_of_pos hb1 hb2 hsp1 hq1
    have hr1 : σ 1 (p ^ a) * (p - 1) * (σ 1 (q ^ b) * (q - 1)) =
        (p - 1) * (q - 1) * (σ 1 (p ^ a) * σ 1 (q ^ b)) := by ring
    have hr2 : p * (p ^ a + 1) * (q * (q ^ b + 1)) =
        p * q * ((p ^ a + 1) * (q ^ b + 1)) := by ring
    rw [hr1, hr2] at h0
    exact h0
  have hchain : 10 * ((p - 1) * (q - 1)) * ((p ^ a + 1) * (q ^ b + 1)) <
      7 * (p * q) * ((p ^ a + 1) * (q ^ b + 1)) := by
    have hcong := congrArg (fun v => v * ((p - 1) * (q - 1))) hpure
    have e1 : 7 * ((p - 1) * (q - 1) * (σ 1 (p ^ a) * σ 1 (q ^ b))) =
        10 * ((p - 1) * (q - 1)) * ((p ^ a + 1) * (q ^ b + 1)) := by
      linear_combination hcong
    rw [← e1]
    have e2 : 7 * ((p - 1) * (q - 1) * (σ 1 (p ^ a) * σ 1 (q ^ b))) <
        7 * (p * q * ((p ^ a + 1) * (q ^ b + 1))) := by
      exact mul_lt_mul_of_pos_left key (by decide : 0 < 7)
    calc 7 * ((p - 1) * (q - 1) * (σ 1 (p ^ a) * σ 1 (q ^ b)))
        < 7 * (p * q * ((p ^ a + 1) * (q ^ b + 1))) := e2
      _ = 7 * (p * q) * ((p ^ a + 1) * (q ^ b + 1)) := by ring
  have hZpos : 0 < (p ^ a + 1) * (q ^ b + 1) :=
    Nat.mul_pos (by omega) (by omega)
  have hfinal : 10 * ((p - 1) * (q - 1)) < 7 * (p * q) := by
    have h := hchain
    have e3 : 10 * ((p - 1) * (q - 1)) * ((p ^ a + 1) * (q ^ b + 1)) =
        (10 * ((p - 1) * (q - 1))) * ((p ^ a + 1) * (q ^ b + 1)) := by ring
    have e4 : 7 * (p * q) * ((p ^ a + 1) * (q ^ b + 1)) =
        (7 * (p * q)) * ((p ^ a + 1) * (q ^ b + 1)) := by ring
    rw [e3, e4] at h
    exact lt_of_mul_lt_mul_right h (Nat.zero_le _)
  -- arithmetic endgame
  rcases le_total p q with hle | hle
  · have hlt : p < q := lt_of_le_of_ne hle hpq
    by_cases hp7 : 7 ≤ p
    · exfalso
      have g1 : 6 * p ≤ 7 * (p - 1) := by omega
      have g2 : 6 * q ≤ 7 * (q - 1) := by omega
      have g3 : (6 * p) * (6 * q) ≤ (7 * (p - 1)) * (7 * (q - 1)) := Nat.mul_le_mul g1 g2
      have g4 : 36 * (p * q) ≤ 49 * ((p - 1) * (q - 1)) := by
        have e1 : (6 * p) * (6 * q) = 36 * (p * q) := by ring
        have e2 : (7 * (p - 1)) * (7 * (q - 1)) = 49 * ((p - 1) * (q - 1)) := by ring
        rwa [e1, e2] at g3
      omega
    · have hp5eq : p = 5 := by
        rcases (by omega : p = 5 ∨ p = 6) with h | h
        · exact h
        · rw [h] at hp
          exact absurd hp (by decide)
      subst hp5eq
      have hq8 : q < 8 := by omega
      rcases (by omega : q = 6 ∨ q = 7) with h | h
      · rw [h] at hq
        exact absurd hq (by decide)
      · exact Or.inl ⟨rfl, h⟩
  · have hlt : q < p := lt_of_le_of_ne hle (Ne.symm hpq)
    by_cases hq7 : 7 ≤ q
    · exfalso
      have g1 : 6 * q ≤ 7 * (q - 1) := by omega
      have g2 : 6 * p ≤ 7 * (p - 1) := by omega
      have g3 : (6 * q) * (6 * p) ≤ (7 * (q - 1)) * (7 * (p - 1)) := Nat.mul_le_mul g1 g2
      have g4 : 36 * (p * q) ≤ 49 * ((p - 1) * (q - 1)) := by
        have e1 : (6 * q) * (6 * p) = 36 * (p * q) := by ring
        have e2 : (7 * (q - 1)) * (7 * (p - 1)) = 49 * ((p - 1) * (q - 1)) := by ring
        rwa [e1, e2] at g3
      omega
    · have hq5eq : q = 5 := by
        rcases (by omega : q = 5 ∨ q = 6) with h | h
        · exact h
        · rw [h] at hq
          exact absurd hq (by decide)
      subst hq5eq
      have hp8 : p < 8 := by omega
      rcases (by omega : p = 6 ∨ p = 7) with h | h
      · rw [h] at hp
        exact absurd hp (by decide)
      · exact Or.inr ⟨h, rfl⟩
