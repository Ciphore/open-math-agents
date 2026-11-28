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


/-- A non-squarefree positive number has a prime whose square divides it. -/
theorem exists_prime_sq_dvd_of_not_squarefree {t : ℕ} (ht : 0 < t) (hnsq : ¬ Squarefree t) :
    ∃ p, p.Prime ∧ p ^ 2 ∣ t := by
  unfold Squarefree at hnsq
  push Not at hnsq
  obtain ⟨x, hxx, hxnu⟩ := hnsq
  have hx1 : x ≠ 1 := by
    intro h1
    subst h1
    exact hxnu isUnit_one
  have hx0 : x ≠ 0 := by
    intro h0
    subst h0
    simp only [mul_zero, Nat.zero_dvd] at hxx
    omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show x ≠ 1 from hx1)
  have hh : p * p ∣ t := (mul_dvd_mul hpdvd hpdvd).trans hxx
  exact ⟨p, hp, by rwa [pow_two]⟩

/-- The one-step repeated-prime extraction: any non-squarefree `t` factors as a maximal
    prime power times a coprime cofactor. -/
theorem repeated_prime_extraction {t : ℕ} (ht : 0 < t) (hnsq : ¬ Squarefree t) :
    ∃ p a u, p.Prime ∧ 2 ≤ a ∧ t = p ^ a * u ∧ ¬ p ∣ u ∧ 0 < u := by
  obtain ⟨p, hp, hpsq⟩ := exists_prime_sq_dvd_of_not_squarefree ht hnsq
  obtain ⟨a, u, hteq, ha, hpu, hu⟩ := exact_power_extraction ht hp hpsq
  exact ⟨p, a, u, hp, ha, hteq, hpu, hu⟩

/-- Iterated extraction for the two-repeated-prime case: given maximal prime-power
    extractions `t = p ^ a * u` and `u = q ^ b * s`, the primes are distinct and the
    kernel `s` is coprime to `p`. -/
theorem two_repeated_extraction {t : ℕ}
    (p a u : ℕ) (hp : p.Prime) (ha : 2 ≤ a) (hteq1 : t = p ^ a * u)
    (hpu : ¬ p ∣ u) (hu : 0 < u)
    (q b s : ℕ) (hq : q.Prime) (hb : 2 ≤ b) (hueq : u = q ^ b * s)
    (hqs : ¬ q ∣ s) (hs : 0 < s) :
    p ≠ q ∧ ¬ p ∣ s ∧ t = p ^ a * (q ^ b * s) := by
  have hpq : p ≠ q := by
    intro h
    subst h
    have hp1 : p ∣ p ^ b := dvd_pow_self p (by omega)
    have hp2 : p ^ b ∣ u := ⟨s, hueq⟩
    exact hpu (dvd_trans hp1 hp2)
  have hps : ¬ p ∣ s := by
    intro hpsdvd
    have hsu : s ∣ u := ⟨q ^ b, by rw [hueq, mul_comm]⟩
    exact hpu (dvd_trans hpsdvd hsu)
  refine ⟨hpq, hps, ?_⟩
  rw [hteq1, hueq]



/-- The one-repeated-prime exclusion: a solution of the ratio equation whose only repeated
    prime power is `p ^ a` (with squarefree coprime kernel) cannot exist, because the local
    equation `7 * σ(p^a) = 10 * (p^a + 1)` contradicts the strict ratio bound at any
    prime `p ≥ 5`. -/
theorem one_prime_exclusion {t p a s : ℕ}
    (ht : 0 < t) (hp : p.Prime) (hp5 : 5 ≤ p) (ha : 2 ≤ a)
    (hsq : Squarefree s) (hps : ¬ p ∣ s) (hs0 : 0 < s)
    (hteq : t = p ^ a * s)
    (heq : 7 * σ 1 t = 10 * usigma t) :
    False := by
  have ht0 : t ≠ 0 := ht.ne'
  have hps_cop : Nat.Coprime p s := (hp.coprime_iff_not_dvd).2 hps
  have hpa_s : Nat.Coprime (p ^ a) s := hps_cop.pow_left a
  have hapos : 0 < a := by omega
  have hppa : IsPrimePow (p ^ a) := (isPrimePow_nat_iff _).2 ⟨p, a, hp, hapos, rfl⟩
  -- sigma factorisation
  have hsg : (σ 1) t = (σ 1) (p ^ a) * (σ 1) s := by
    rw [hteq]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hpa_s
  -- unitary factorisation
  have hug : usigma t = usigma s * (p ^ a + 1) := by
    have hcomm : t = s * p ^ a := by rw [hteq]; ring
    rw [hcomm, unitarySum hs0 hppa hpa_s]
  -- squarefree kernel: unitary divisors are all divisors
  have hsf : usigma s = (σ 1) s := usigma_eq_sigma_of_squarefree hsq
  have hspos : 0 < (σ 1) s := sigma_pos' s hs0.ne'
  -- the pure single-prime equation
  have hpure : 7 * (σ 1) (p ^ a) = 10 * (p ^ a + 1) := by
    rw [hsg, hug, hsf] at heq
    -- heq : 7 * ((σ 1)(p^a) * (σ 1) s) = 10 * ((σ 1) s * (p^a+1))
    have h1 : 7 * ((σ 1) (p ^ a) * (σ 1) s) = (7 * (σ 1) (p ^ a)) * (σ 1) s := by ring
    have h2 : 10 * ((σ 1) s * (p ^ a + 1)) = (10 * (p ^ a + 1)) * (σ 1) s := by ring
    rw [h1, h2] at heq
    exact Nat.eq_of_mul_eq_mul_right hspos heq
  -- strict ratio bound at the prime power
  have hb1 : (σ 1) (p ^ a) * (p - 1) < p * (p ^ a + 1) := ratio_bound (e := a) hp
  -- multiply bound by 7 and substitute the pure equation
  have key : 7 * ((σ 1) (p ^ a) * (p - 1)) < 7 * (p * (p ^ a + 1)) :=
    mul_lt_mul_of_pos_left hb1 (by decide : 0 < 7)
  have e1 : 7 * ((σ 1) (p ^ a) * (p - 1)) = (7 * (σ 1) (p ^ a)) * (p - 1) := by ring
  rw [e1, hpure] at key
  -- key : 10 * (p^a+1) * (p-1) < 7 * (p * (p^a+1))
  have hZpos : 0 < p ^ a + 1 := by omega
  have e3 : 10 * (p ^ a + 1) * (p - 1) = (10 * (p - 1)) * (p ^ a + 1) := by ring
  have e4 : 7 * (p * (p ^ a + 1)) = (7 * p) * (p ^ a + 1) := by ring
  rw [e3, e4] at key
  have hfinal : 10 * (p - 1) < 7 * p := lt_of_mul_lt_mul_right key (Nat.zero_le _)
  omega
