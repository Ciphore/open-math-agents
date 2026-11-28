import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1_H2_R1

-- Proof of OeisA63880.mod_216_of_a.R1.H1.R2.H2.R1.H2.R1.H1
-- Credit: @Ciphore
-- A powerful odd number whose prime exponents are all even is a perfect square in
-- factorization form. Each geometric sum in the divisor-sum product then has an odd
-- number of odd terms, so `σ` is odd — but the equation `σ = 2 * usigma` forces it even.

open OeisA63880
open scoped ArithmeticFunction.sigma

theorem even_increment (p e : ℕ) : Even (p ^ (2 * e + 1) + p ^ (2 * e + 2)) := by
  have hfact : p ^ (2 * e + 1) + p ^ (2 * e + 2) = p ^ (2 * e) * (p * (p + 1)) := by
    have e1 : p ^ (2 * e + 1) = p ^ (2 * e) * p := pow_succ p (2 * e)
    have e2 : p ^ (2 * e + 2) = p ^ (2 * e + 1) * p := by
      rw [show 2 * e + 2 = 2 * e + 1 + 1 from by ring]
      exact pow_succ p (2 * e + 1)
    rw [e2, e1]
    ring
  rw [hfact]
  have hpp : Even (p * (p + 1)) := by
    rcases Nat.even_or_odd p with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨r * (p + 1), by rw [hr]; ring⟩
    · exact ⟨p * (r + 1), by rw [hr]; ring⟩
  exact Even.mul_left hpp _

theorem odd_geom (p e : ℕ) : Odd (∑ i ∈ Finset.range (2 * e + 1), p ^ i) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 : 2 * (e + 1) + 1 = (2 * e + 1 + 1) + 1 := by ring
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
    exact Odd.add_even ih (even_increment p e)

theorem odd_prod {s : Finset ℕ} {f : ℕ → ℕ} (h : ∀ x ∈ s, Odd (f x)) :
    Odd (∏ x ∈ s, f x) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has]
    exact Odd.mul (h a (Finset.mem_insert_self a s))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

/-- If every prime factor of nonzero `d` occurs to an even exponent, `σ(d)` is odd. -/
theorem odd_sigma_of_even_factorization {d : ℕ} (hd0 : d ≠ 0)
    (hall : ∀ q : ℕ, q.Prime → q ∣ d → Even (d.factorization q)) : Odd (σ 1 d) := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors hd0]
  apply odd_prod
  intro p hp
  have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hexp : Even (d.factorization p) := hall p hpprime hpd
  obtain ⟨e, he⟩ := hexp
  have he2 : d.factorization p + 1 = 2 * e + 1 := by omega
  rw [he2]
  exact odd_geom p e

/-- The even-exponent case of the powerful-core problem. -/
theorem powerful_even_case : ∀ d : ℕ, Odd d →
    (∀ q : ℕ, q.Prime → q ∣ d → 2 ≤ d.factorization q) →
    (∀ q : ℕ, q.Prime → q ∣ d → Even (d.factorization q)) → ¬ OeisA63880.A d := by
  intro d hod hpow hall hA
  have hd0 : d ≠ 0 := hA.1.ne'
  have hodd : Odd (σ 1 d) := odd_sigma_of_even_factorization hd0 hall
  have heven : Even (σ 1 d) := ⟨usigma d, by rw [hA.2]; ring⟩
  exact Nat.not_even_iff_odd.mpr hodd heven

theorem main : OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1_H2_R1.H1 :=
  powerful_even_case
