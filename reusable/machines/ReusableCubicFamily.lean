import Formalizations.Reusable.Polynomial

open Formalizations.Reusable Polynomial

/-- A parameter interval certified by four fixed, exactly checked sign witnesses. -/
theorem cubic_family_three_distinct_real_roots (c : ℝ) (hlo : -2 < c) (hhi : c < 2) :
    3 ≤ ((X ^ 3 - C 3 * X + C c : ℝ[X]).roots.toFinset.card) := by
  let p : ℝ[X] := X ^ 3 - C 3 * X + C c
  have hp : p ≠ 0 := by
    intro h
    have he : p.eval 2 = 0 := by simp [h]
    have hv : p.eval 2 = c + 2 := by simp [p]; ring
    linarith
  refine card_roots_toFinset_ge_of_alternating_sign p hp 3 ![-2, -1, 1, 2] ?_ ?_
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num [p, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow] <;> nlinarith

private theorem cubic_family_monic_degree (c : ℝ) :
    (X ^ 3 - C 3 * X + C c : ℝ[X]).Monic ∧
    (X ^ 3 - C 3 * X + C c : ℝ[X]).natDegree = 3 := by
  rw [sub_eq_add_neg, add_assoc]
  have hlower : (-(C 3 * X) + C c : ℝ[X]).natDegree < (X ^ 3 : ℝ[X]).natDegree := by
    refine (natDegree_add_le _ _).trans_lt ?_
    norm_num [natDegree_C_mul_X]
  exact ⟨(monic_X_pow 3).add_of_left (degree_lt_degree hlower),
    by rw [natDegree_add_eq_left_of_natDegree_lt hlower, natDegree_X_pow]⟩

/-- The same four sign witnesses and the degree bound certify real splitting (R0007). -/
theorem cubic_family_splits (c : ℝ) (hlo : -2 < c) (hhi : c < 2) :
    (X ^ 3 - C 3 * X + C c : ℝ[X]).Splits := by
  let p : ℝ[X] := X ^ 3 - C 3 * X + C c
  obtain ⟨hp, hdeg⟩ := cubic_family_monic_degree c
  refine splits_of_alternating_sign p hp.ne_zero 3 hdeg.le ![-2, -1, 1, 2] ?_ ?_
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num [p, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow] <;> nlinarith

/-- Real splitting and monicity give Newton's inequality at index one (R0015).
It holds throughout the interval but gives no new restriction on `c`: Vieta gives `e₁ = 0`, `e₂ = -3`. -/
theorem cubic_family_newton_at_one (c : ℝ) (hlo : -2 < c) (hhi : c < 2) :
    let p : ℝ[X] := X ^ 3 - C 3 * X + C c
    (p.roots.esymm 1) ^ 2 * 3 ≥ p.roots.esymm 2 * 9 := by
  obtain ⟨hp, hdeg⟩ := cubic_family_monic_degree c
  have htwo : 1 + 1 ≤ (X ^ 3 - C 3 * X + C c : ℝ[X]).natDegree := by
    rw [hdeg]
    decide
  have h := newton_inequality_esymm_roots (cubic_family_splits c hlo hhi) hp (k := 1) le_rfl htwo
  norm_num [hdeg] at h
  exact h

/-- At the two boundary parameters the cubic acquires a repeated root. -/
example (t : ℝ) : t ^ 3 - 3 * t + 2 = (t - 1) ^ 2 * (t + 2) := by ring

example (t : ℝ) : t ^ 3 - 3 * t - 2 = (t + 1) ^ 2 * (t - 2) := by ring
