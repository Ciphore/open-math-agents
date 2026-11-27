import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1

-- Step Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1
-- Credit: @Ciphore
-- H2 := eventually, 3 * N.sqrt.sqrt < N^(3/10) where N = 8m+3

open Real Filter

/-- Cast of a natural square root is bounded by the real square root. -/
lemma nat_sqrt_le_real_sqrt (n : ℕ) : (n.sqrt : ℝ) ≤ Real.sqrt n := by
  have h1 : ((n.sqrt : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have := Nat.sqrt_le' n
    have hcast : ((n.sqrt ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    simpa using hcast
  have h2 : (n.sqrt : ℝ) = Real.sqrt ((n.sqrt : ℝ) ^ 2) :=
    (Real.sqrt_sq (by positivity)).symm
  rw [h2]
  exact Real.sqrt_le_sqrt h1

/-- The double natural square root is bounded by the real fourth root. -/
lemma nat_sqrt_sqrt_le (n : ℕ) : (n.sqrt.sqrt : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have h1 : (n.sqrt.sqrt : ℝ) ≤ Real.sqrt (n.sqrt : ℝ) := nat_sqrt_le_real_sqrt n.sqrt
  have h2 : Real.sqrt (n.sqrt : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) :=
    Real.sqrt_le_sqrt (nat_sqrt_le_real_sqrt n)
  have h3 : Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    norm_num
  exact h1.trans (h2.trans h3.le)

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1.H2
  rw [eventually_atTop]
  refine ⟨3486784401, fun m hm => ?_⟩
  dsimp only
  have hN : (3 : ℝ) ^ (20 : ℕ) < ((8 * m + 3 : ℕ) : ℝ) := by
    have hm' : (3486784401 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h1 : ((8 * m + 3 : ℕ) : ℝ) = 8 * (m : ℝ) + 3 := by norm_num
    rw [h1]
    have : (3 : ℝ) ^ (20 : ℕ) = 3486784401 := by norm_num
    linarith
  set x := ((8 * m + 3 : ℕ) : ℝ) with hx
  have hxpos : (0 : ℝ) < x := by positivity
  -- key: 3 * sqrt.sqrt <= 3 * x^(1/4) < x^(3/10)
  have hcast : ((8 * m + 3).sqrt.sqrt : ℝ) = ((8 * m + 3 : ℕ).sqrt.sqrt : ℝ) := rfl
  rw [hcast]
  have step1 : ((8 * m + 3 : ℕ).sqrt.sqrt : ℝ) * 3 ≤ x ^ ((1 : ℝ) / 4) * 3 := by
    have h := nat_sqrt_sqrt_le (8 * m + 3)
    have : (((8 * m + 3 : ℕ) : ℝ)) = x := rfl
    rw [this] at h
    exact mul_le_mul_of_nonneg_right h (by norm_num)
  have key : (3 : ℝ) < x ^ ((1 : ℝ) / 20) := by
    have h20 : (3 : ℝ) = ((3 : ℝ) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) := by
      rw [← Real.rpow_natCast 3 20]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num
    rw [h20]
    exact Real.rpow_lt_rpow (by positivity) hN (by norm_num)
  have step2 : x ^ ((1 : ℝ) / 4) * 3 < x ^ ((3 : ℝ) / 10) := by
    have hsplit : x ^ ((3 : ℝ) / 10) = x ^ ((1 : ℝ) / 4) * x ^ ((1 : ℝ) / 20) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      norm_num
    rw [hsplit]
    have hpos : (0 : ℝ) < x ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hxpos _
    exact mul_lt_mul_of_pos_left key hpos
  calc (3 : ℝ) * ((8 * m + 3 : ℕ).sqrt.sqrt : ℝ)
      = ((8 * m + 3 : ℕ).sqrt.sqrt : ℝ) * 3 := by ring
    _ ≤ x ^ ((1 : ℝ) / 4) * 3 := step1
    _ < x ^ ((3 : ℝ) / 10) := step2
