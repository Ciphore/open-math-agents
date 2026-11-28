import OMAReductions.R_opg_strange_series_R1

-- Reduction opg-strange-series.R1.H2.R1 of step opg-strange-series.R1.H2
-- Credit: @Ciphore

/-!
# Collatz descent core: the first modulo-128 refinement

The remaining residue classes `7, 15, 27, 31 (mod 32)` split into sixteen classes modulo
`128`. Three of those classes descend by explicit affine iteration:

* `7 (mod 128)` reaches a smaller value in eleven steps;
* `15 (mod 128)` reaches a smaller value in eleven steps;
* `59 (mod 128)` reaches a smaller value in eleven steps.

The other thirteen classes remain open. They are grouped by the original modulo-32 class so
that the four residual cores can be attacked independently.
-/

namespace OMA.R_opg_strange_series_R1_H2_R1

open OMA.S_opg_strange_series

/-- Every input congruent to `7` modulo `128` descends in eleven steps. -/
lemma descent_seven {n : ℕ} (_hn : 1 < n) (hr : n % 128 = 7) :
    ∃ k : ℕ, f^[k] n < n := by
  have fe : ∀ x, x % 2 = 0 → x ≠ 1 → f x = x / 2 := by
    intro x h1 h2
    simp [f, h2, h1]
  have fo : ∀ x, x % 2 = 1 → x ≠ 1 → f x = 3 * x + 1 := by
    intro x h1 h2
    simp [f, h2, h1]
  refine ⟨11, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [fo (n) (by omega) (by omega), fe ((3 * n + 1)) (by omega) (by omega), fo (((3 * n + 1) / 2)) (by omega) (by omega), fe ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), fo (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), fe ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), fe (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), fo ((((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), fe ((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), fe (((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega), fe ((((3 * (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `15` modulo `128` descends in eleven steps. -/
lemma descent_fifteen {n : ℕ} (_hn : 1 < n) (hr : n % 128 = 15) :
    ∃ k : ℕ, f^[k] n < n := by
  have fe : ∀ x, x % 2 = 0 → x ≠ 1 → f x = x / 2 := by
    intro x h1 h2
    simp [f, h2, h1]
  have fo : ∀ x, x % 2 = 1 → x ≠ 1 → f x = 3 * x + 1 := by
    intro x h1 h2
    simp [f, h2, h1]
  refine ⟨11, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [fo (n) (by omega) (by omega), fe ((3 * n + 1)) (by omega) (by omega), fo (((3 * n + 1) / 2)) (by omega) (by omega), fe ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), fo (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), fe ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), fo (((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), fe ((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1)) (by omega) (by omega), fe (((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), fe ((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), fe (((((3 * ((3 * ((3 * ((3 * n + 1) / 2) + 1) / 2) + 1) / 2) + 1) / 2) / 2) / 2)) (by omega) (by omega)]
  omega


/-- Every input congruent to `59` modulo `128` descends in eleven steps. -/
lemma descent_fiftynine {n : ℕ} (_hn : 1 < n) (hr : n % 128 = 59) :
    ∃ k : ℕ, f^[k] n < n := by
  have fe : ∀ x, x % 2 = 0 → x ≠ 1 → f x = x / 2 := by
    intro x h1 h2
    simp [f, h2, h1]
  have fo : ∀ x, x % 2 = 1 → x ≠ 1 → f x = 3 * x + 1 := by
    intro x h1 h2
    simp [f, h2, h1]
  refine ⟨11, ?_⟩
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [fo (n) (by omega) (by omega), fe ((3 * n + 1)) (by omega) (by omega), fo (((3 * n + 1) / 2)) (by omega) (by omega), fe ((3 * ((3 * n + 1) / 2) + 1)) (by omega) (by omega), fe (((3 * ((3 * n + 1) / 2) + 1) / 2)) (by omega) (by omega), fo ((((3 * ((3 * n + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega), fe ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1)) (by omega) (by omega), fo (((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2)) (by omega) (by omega), fe ((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1)) (by omega) (by omega), fe (((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2)) (by omega) (by omega), fe ((((3 * ((3 * (((3 * ((3 * n + 1) / 2) + 1) / 2) / 2) + 1) / 2) + 1) / 2) / 2)) (by omega) (by omega)]
  omega

/-- Residual core descending from `7 (mod 32)`, apart from the eliminated class
`7 (mod 128)`. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n % 32 = 7 → n % 128 ≠ 7 → ∃ k : ℕ, f^[k] n < n

/-- Residual core descending from `15 (mod 32)`, apart from the eliminated class
`15 (mod 128)`. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → n % 32 = 15 → n % 128 ≠ 15 → ∃ k : ℕ, f^[k] n < n

/-- Residual core descending from `27 (mod 32)`, apart from the eliminated class
`59 (mod 128)`. -/
def H3 : Prop :=
  ∀ n : ℕ, 1 < n → n % 32 = 27 → n % 128 ≠ 59 → ∃ k : ℕ, f^[k] n < n

/-- Residual core descending from `31 (mod 32)`. -/
def H4 : Prop :=
  ∀ n : ℕ, 1 < n → n % 32 = 31 → ∃ k : ℕ, f^[k] n < n

theorem main : H1 → H2 → H3 → H4 → OMA.R_opg_strange_series_R1.H2 := by
  intro h7core h15core h27core h31core n hn hc
  rcases hc with h7 | h15 | h27 | h31
  · by_cases hlow : n % 128 = 7
    · exact descent_seven hn hlow
    · exact h7core n hn h7 hlow
  · by_cases hlow : n % 128 = 15
    · exact descent_fifteen hn hlow
    · exact h15core n hn h15 hlow
  · by_cases hlow : n % 128 = 59
    · exact descent_fiftynine hn hlow
    · exact h27core n hn h27 hlow
  · exact h31core n hn h31

end OMA.R_opg_strange_series_R1_H2_R1
