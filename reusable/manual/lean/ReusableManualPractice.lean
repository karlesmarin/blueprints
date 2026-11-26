/-
Practical examples of the Reusable-layer manual (chapter «Practical examples, start to finish»): concrete problems
solved end to end with theorems of the layer. Every example here is checked by Lean; the manual shows exactly this code.
-/
import Formalizations.Reusable

open Formalizations.Reusable Matrix Polynomial
open scoped Kronecker

/-! ### Example 1 — your own lemma on top of the layer, then a concrete cubic -/

/-- Four increasing points where a nonzero real polynomial alternates in sign give three distinct real roots. -/
theorem three_real_roots (p : ℝ[X]) (hp : p ≠ 0) (a b c d : ℝ) (h1 : a < b) (h2 : b < c) (h3 : c < d)
    (s1 : p.eval a * p.eval b < 0) (s2 : p.eval b * p.eval c < 0) (s3 : p.eval c * p.eval d < 0) :
    3 ≤ p.roots.toFinset.card := by
  refine card_roots_toFinset_ge_of_alternating_sign p hp 3 ![a, b, c, d] ?_ ?_
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i
    · simpa using h1
    · simpa using h2
    · simpa using h3
  · intro i
    fin_cases i
    · simpa using s1
    · simpa using s2
    · simpa using s3

/-- `X³ − 3X + 1` has three distinct real roots: its values at `−2, 0, 1, 2` are `−1, 1, −1, 3`. -/
example : 3 ≤ ((X ^ 3 - C 3 * X + 1 : ℝ[X]).roots.toFinset.card) := by
  have hne : (X ^ 3 - C 3 * X + 1 : ℝ[X]) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  exact three_real_roots _ hne (-2) 0 1 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-! ### Example 2 — a classical bound for every triangle -/

/-- `cos A + cos B + cos C ≤ 3/2` for the angles of a triangle: Recipe 1 with `x = y = z = 1`. -/
example (A B C : ℝ) (h : A + B + C = Real.pi) : Real.cos A + Real.cos B + Real.cos C ≤ 3 / 2 := by
  have key := wolstenholme_defect_eq_sq_add_sq 1 1 1 A B C h
  nlinarith [key, sq_nonneg (1 - 1 * Real.cos B - 1 * Real.cos C), sq_nonneg (1 * Real.sin B - 1 * Real.sin C)]

/-! ### Example 3 — the rank of a tensor product without writing the matrix -/

/-- The Kronecker product of the `2 × 2` and `3 × 3` identities is a `6 × 6` matrix of rank `2 · 3 = 6`. -/
example : ((1 : Matrix (Fin 2) (Fin 2) ℚ) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℚ)).rank = 6 := by
  rw [matrix_rank_kronecker]
  simp [rank_one]

/-! ### Example 4 — Bell numbers modulo a prime -/

/-- `B(7) ≡ 2 (mod 7)` (indeed `B(7) = 877`): Touchard's congruence with `n = 0`. -/
example : ((Nat.bell 7 : ℕ) : ZMod 7) = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := touchard_bell_add_prime 7 0
  rw [zero_add, Nat.bell_zero, zero_add, Nat.bell_one] at h
  rw [h]
  rfl

/-! ### Example 5 — a central binomial coefficient modulo `p³` -/

/-- `C(26, 13) ≡ 2 (mod 13³)`: the second congruence of Wolstenholme's theorem with `p = 13`. -/
example : Nat.choose 26 13 ≡ 2 [MOD 13 ^ 3] :=
  (wolstenholme_choose_modEq 13 (by norm_num) (by norm_num)).2

/-! ### Example 6 — an exact trigonometric product -/

/-- `2 sin(π/3) · 2 sin(2π/3) = 3`: the case `n = 3` of `∏ 2 sin(kπ/n) = n`. -/
example : ∏ k ∈ Finset.Ico (1 : ℕ) 3, 2 * Real.sin (k * Real.pi / 3) = 3 := by
  have h := prod_two_sin_mul_pi_div 3 (by norm_num)
  exact_mod_cast h
