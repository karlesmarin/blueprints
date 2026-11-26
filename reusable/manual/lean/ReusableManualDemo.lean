/-
Demos of the Reusable-layer manual (one per recipe): the code a reader pastes into a file of their own project. Every
example here is checked by Lean; the manual shows exactly this code.
-/
import Formalizations.Reusable

open Formalizations.Reusable Matrix Polynomial

/-! ### Section 5 — the first theorem -/

example : Nat.choose 13 6 ≡ 1 [MOD 7 ^ 3] :=
  (wolstenholme_choose_modEq 7 (by norm_num) (by norm_num)).1

/-! ### Section 7 — ways of using a theorem -/

example (A B : Matrix (Fin 2) (Fin 3) ℚ) : (A + B).rank ≤ A.rank + B.rank :=
  matrix_rank_add_le A B

example (A : Matrix (Fin 2) (Fin 3) ℚ) : (A + A).rank ≤ 2 * A.rank := by
  have := matrix_rank_add_le A A
  omega

/-! ### Recipe 1 — an inequality of a triangle in two lines (Wolstenholme) -/

/-- For the angles of a triangle and any real `x, y, z`: `2yz cos A + 2zx cos B + 2xy cos C ≤ x² + y² + z²`. -/
example (x y z A B C : ℝ) (h : A + B + C = Real.pi) :
    2 * y * z * Real.cos A + 2 * z * x * Real.cos B + 2 * x * y * Real.cos C
      ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  have key := wolstenholme_defect_eq_sq_add_sq x y z A B C h
  nlinarith [sq_nonneg (x - z * Real.cos B - y * Real.cos C),
    sq_nonneg (z * Real.sin B - y * Real.sin C)]

/-! ### Recipe 2 — real roots counted by sign changes -/

/-- `X² − 2` has at least two distinct real roots: it changes sign on `(−2, 0)` and on `(0, 2)`. -/
example : 2 ≤ ((X ^ 2 - C 2 : ℝ[X]).roots.toFinset.card) := by
  have hne : (X ^ 2 - C 2 : ℝ[X]) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  refine card_roots_toFinset_ge_of_alternating_sign _ hne 2 ![-2, 0, 2] ?_ ?_
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num

/-! ### Recipe 3 — the coefficients of a real-rooted polynomial (Newton) -/

/-- For a monic real polynomial with only real roots and degree `n ≥ 2`, the elementary symmetric
functions of its roots satisfy Newton's inequality `e₁² · C(n,0) C(n,2) ≥ e₀ e₂ · C(n,1)²`. -/
example (p : ℝ[X]) (hp : p.Splits) (hm : p.Monic) (h2 : 2 ≤ p.natDegree) :
    (p.roots.esymm 1) ^ 2 * ((p.natDegree.choose 0 : ℝ) * (p.natDegree.choose 2 : ℝ))
      ≥ (p.roots.esymm 0) * (p.roots.esymm 2) * ((p.natDegree.choose 1 : ℝ)) ^ 2 :=
  newton_inequality_esymm_roots hp hm le_rfl h2

/-! ### Recipe 4 — a certificate that a quadratic form is a sum of `k` squares -/

/-- A symmetric matrix whose characteristic polynomial has alternating signs is positive semidefinite, and then a
rank-`k` one has a quadratic form that is a sum of exactly `k` squares of linear forms. Two steps, two theorems. -/
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : A.IsSymm)
    (halt : ∀ k ≤ A.charpoly.natDegree, 0 ≤ (-1 : ℝ) ^ (A.charpoly.natDegree - k) * A.charpoly.coeff k)
    (k : ℕ) (hk : A.rank = k) :
    ∃ v : Fin k → (n → ℝ), ∀ u, u ⬝ᵥ (A *ᵥ u) = ∑ i, (v i ⬝ᵥ u) ^ 2 :=
  psd_quadForm_eq_sum_rank_sq (posSemidef_of_charpoly_alternating hA halt) hk

/-! ### Recipe 5 — a congruence of Wolstenholme -/

/-- `C(13, 6) ≡ 1 (mod 7³)`: the case `p = 7` of Wolstenholme's theorem. -/
example : Nat.choose 13 6 ≡ 1 [MOD 7 ^ 3] :=
  (wolstenholme_choose_modEq 7 (by norm_num) (by norm_num)).1

/-! ### Recipe 6 — rank bounds for block matrices -/

/-- A block upper-triangular matrix with identity diagonal blocks has full rank, whatever its corner `B`. -/
example (B : Matrix (Fin 2) (Fin 2) ℚ) :
    4 ≤ (fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℚ) B 0 (1 : Matrix (Fin 2) (Fin 2) ℚ)).rank := by
  have h := matrix_rank_add_rank_le_rank_fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℚ) B
    (1 : Matrix (Fin 2) (Fin 2) ℚ)
  simpa only [rank_one, Fintype.card_fin] using h
