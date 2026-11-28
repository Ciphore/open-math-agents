import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H3_R1_H3_R1

-- Proof of OeisA63880.mod_216_of_a.R1.H3.R1.H3.R1.H1
-- Credit: @Ciphore
-- For squarefree `t` every divisor is unitary, so `usigma t = σ 1 t` and the
-- transformed equation `91 * σ 1 t = 100 * usigma t` collapses to `91 = 100`.

open OeisA63880
open scoped ArithmeticFunction.sigma

/-- For squarefree `t`, every divisor is unitary. -/
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

/-- For squarefree `t`, the unitary and ordinary divisor sums agree. -/
theorem usigma_eq_sigma_of_squarefree {t : ℕ} (hsq : Squarefree t) :
    usigma t = σ 1 t := by
  unfold usigma
  rw [sqfree_unitaryDivisors hsq, ArithmeticFunction.sigma_one_apply]

/-- The squarefree case of the transformed ratio equation is impossible:
it would force `91 = 100`. -/
theorem squarefree_case_impossible :
    OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H3_R1.H1 := by
  intro t htodd ht3 hsq hnp hr
  have huv := usigma_eq_sigma_of_squarefree hsq
  rw [huv] at hr
  have hpos : 0 < σ 1 t := by
    obtain ⟨k, hk⟩ := htodd
    have ht0 : t ≠ 0 := by omega
    rw [ArithmeticFunction.sigma_one_apply]
    have hmem : t ∈ t.divisors := Nat.mem_divisors.2 ⟨dvd_rfl, ht0⟩
    have hle : t ≤ ∑ d ∈ t.divisors, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hmem
    omega
  have h91 : 91 * σ 1 t = 100 * σ 1 t := hr
  have : 91 = 100 := Nat.eq_of_mul_eq_mul_right hpos h91
  norm_num at this
