import Formalizations.Reusable.LinearAlgebra

/- Exact cross-check from Excovery: `python -m excovery.charpoly_psd '[[2,1],[1,2]]'`
   gives a symmetric PSD matrix of rank 2, with characteristic coefficients [1, -4, 3].
   Verified with `lake env lean` in formalizations v0.15.0. -/

open Formalizations.Reusable Matrix Polynomial

private def A : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]

private theorem aSymm : A.IsSymm := by
  change A.transpose = A
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem aDet : A.det = 3 := by
  norm_num [A, Matrix.det_fin_two]

private theorem aCharpoly : A.charpoly = X ^ 2 - C 4 * X + C 3 := by
  have traceA : A.trace = 4 := by
    norm_num [A, Matrix.trace, Fin.sum_univ_two]
  rw [Matrix.charpoly_fin_two, traceA, aDet]

private theorem aSigns :
    ∀ k ≤ A.charpoly.natDegree, 0 ≤ (-1 : ℝ) ^ (A.charpoly.natDegree - k) * A.charpoly.coeff k := by
  have degreeA : A.charpoly.natDegree = 2 := by
    simp [Matrix.charpoly_natDegree_eq_dim]
  intro k hk
  rw [degreeA] at hk ⊢
  rw [aCharpoly]
  interval_cases k <;> norm_num [coeff_X_pow, coeff_C_mul_X, coeff_C]

private theorem aRank : A.rank = 2 := by
  have detNonzero : A.det ≠ 0 := by
    rw [aDet]
    norm_num
  simpa using Matrix.rank_of_det_ne_zero detNonzero

-- R0032 supplies the positivity required by R0033.
example : ∃ v : Fin 2 → (Fin 2 → ℝ), ∀ u, u ⬝ᵥ (A *ᵥ u) = ∑ i, (v i ⬝ᵥ u) ^ 2 :=
  psd_quadForm_eq_sum_rank_sq (posSemidef_of_charpoly_alternating aSymm aSigns) aRank

-- The explicit diagonal expression shown in the video.
example (u : Fin 2 → ℝ) :
    u ⬝ᵥ (A *ᵥ u) = (3 / 2) * (u 0 + u 1) ^ 2 + (1 / 2) * (u 0 - u 1) ^ 2 := by
  simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring
