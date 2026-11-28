import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H3_R1_H2_R1

-- Proof of OeisA63880.mod_216_of_a.R1.H3.R1.H2.R1.H1
-- Credit: @Ciphore
-- The equation `7 * σ 1 t = 10 * usigma t` forces `10 ∣ σ 1 t`, so `σ 1 t` is even.
-- But a nonzero perfect square has odd sigma: in the prime-factorization product each
-- factor is a geometric sum of an odd number of consecutive prime powers, hence odd.

open OeisA63880
open OeisA63880
open scoped ArithmeticFunction.sigma

/-- The product `p * (p+1)` of consecutive naturals is even. -/
theorem even_mul_succ (p : ℕ) : Even (p * (p + 1)) := by
  rcases Nat.even_or_odd p with hp | hp
  · exact Even.mul_right hp _
  · have h : Even (p + 1) := hp.add_odd odd_one
    exact Even.mul_left h _

/-- Two consecutive powers with odd starting exponent sum to an even number. -/
theorem even_increment (p e : ℕ) : Even (p ^ (2 * e + 1) + p ^ (2 * e + 2)) := by
  have hfact : p ^ (2 * e + 1) + p ^ (2 * e + 2) = p ^ (2 * e) * (p * (p + 1)) := by
    have e1 : p ^ (2 * e + 1) = p ^ (2 * e) * p := pow_succ p (2 * e)
    have e2 : p ^ (2 * e + 2) = p ^ (2 * e + 1) * p := by
      rw [show 2 * e + 2 = 2 * e + 1 + 1 from by ring]
      exact pow_succ p (2 * e + 1)
    rw [e2, e1]
    ring
  rw [hfact]
  exact Even.mul_left (even_mul_succ p) _

/-- The geometric sum of an odd number of consecutive powers is always odd. -/
theorem odd_geom (p e : ℕ) : Odd (∑ i ∈ Finset.range (2 * e + 1), p ^ i) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 : 2 * (e + 1) + 1 = (2 * e + 1 + 1) + 1 := by ring
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
    exact Odd.add_even ih (even_increment p e)

/-- Product of odd values is odd. -/
theorem odd_prod {s : Finset ℕ} {f : ℕ → ℕ} (h : ∀ x ∈ s, Odd (f x)) :
    Odd (∏ x ∈ s, f x) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has]
    exact Odd.mul (h a (Finset.mem_insert_self a s))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

/-- A nonzero perfect square has odd sigma. -/
theorem odd_sigma_of_square {t : ℕ} (ht : IsSquare t) (ht0 : t ≠ 0) : Odd (σ 1 t) := by
  obtain ⟨s, rfl⟩ := ht
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors ht0]
  apply odd_prod
  intro p hp
  have hexp : Even ((s * s).factorization p) := by
    have h2 : s * s = s ^ 2 := (pow_two s).symm
    rw [h2, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, nsmul_eq_mul]
    exact even_two_mul _
  obtain ⟨e, he⟩ := hexp
  have he2 : (s * s).factorization p + 1 = 2 * e + 1 := by omega
  rw [he2]
  exact odd_geom p e

/-- Perfect squares cannot satisfy the core ratio equation. -/
theorem not_square_of_ratio {t : ℕ} (ht0 : t ≠ 0)
    (ht : 7 * σ 1 t = 10 * usigma t) : ¬ IsSquare t := by
  intro hsq
  have hodd := odd_sigma_of_square hsq ht0
  have h10 : 10 ∣ σ 1 t := by
    have h107 : 10 ∣ 7 * σ 1 t := by
      rw [ht]
      exact dvd_mul_right 10 _
    exact Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 10 7) h107
  obtain ⟨m, hm⟩ := h10
  have hev : Even (σ 1 t) := ⟨5 * m, by rw [hm]; ring⟩
  exact Nat.not_even_iff_odd.mpr hodd hev

theorem main : OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H2_R1.H1 := by
  intro t hodd h3 hnsf hnpp hsq heq
  have ht0 : t ≠ 0 := by
    rcases hodd with ⟨k, hk⟩
    omega
  exact (not_square_of_ratio ht0 heq) hsq
