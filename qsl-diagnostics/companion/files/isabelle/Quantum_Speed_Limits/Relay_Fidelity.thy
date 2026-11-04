(* encaje: teoria Isabelle de la cola (formalizacion), compilada con isa_compilar.py; no es herramienta. *)
theory Relay_Fidelity
  imports "HOL-Analysis.Analysis"
begin

text \<open>
Bridge between a single excitation transfer and the fidelity of the reduced channel at the receiver B.
The input qubit state is alpha times ket 0 plus beta times ket 1, with alpha and beta complex.
The state reaching B is the two by two density matrix with entries
1 minus the square of the modulus of beta times P, then alpha times conjugate beta times conjugate w,
then conjugate alpha times beta times w, then the square of the modulus of beta times P.
Here P is the transferred population for input ket 1 and w is the complex coherence for the input
equal superposition, up to the factor 2. The fidelity is the expectation of this matrix in the input state.
We model the matrix entries and the quadratic form explicitly with complex numbers.
\<close>

section \<open>The reduced density matrix and the fidelity\<close>

definition rho00 :: "complex \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> complex" where
  "rho00 a b P = 1 - of_real ((norm b)\<^sup>2 * P)"

definition rho01 :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex" where
  "rho01 a b w = a * cnj b * cnj w"

definition rho10 :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex" where
  "rho10 a b w = cnj a * b * w"

definition rho11 :: "complex \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> complex" where
  "rho11 a b P = of_real ((norm b)\<^sup>2 * P)"

text \<open>The fidelity is the expectation of the matrix in the input vector (alpha, beta),
that is conjugate of the vector, times the matrix, times the vector.\<close>

definition fid :: "complex \<Rightarrow> complex \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> complex" where
  "fid a b P w =
     cnj a * (rho00 a b P * a + rho01 a b w * b) + cnj b * (rho10 a b w * a + rho11 a b P * b)"

section \<open>1. Closed form\<close>

text \<open>The closed form is: modulus of alpha squared times (1 minus modulus of beta squared times P),
plus modulus of beta to the fourth times P, plus twice modulus of alpha squared times modulus of beta squared
times the real part of w. The cross terms are conjugate to each other, so the fidelity is real.\<close>

lemma fid_formula:
  "fid a b P w =
     of_real ((norm a)\<^sup>2 * (1 - (norm b)\<^sup>2 * P) + (norm b)\<^sup>2 * (norm b)\<^sup>2 * P
              + 2 * (norm a)\<^sup>2 * (norm b)\<^sup>2 * Re w)"
proof -
  have ha: "cnj a * a = of_real ((norm a)\<^sup>2)"
    by (simp only: mult.commute complex_norm_square)
  have hb: "cnj b * b = of_real ((norm b)\<^sup>2)"
    by (simp only: mult.commute complex_norm_square)
  have hw: "w + cnj w = of_real (2 * Re w)"
    by (simp only: complex_add_cnj of_real_mult of_real_numeral)
  have step1: "fid a b P w =
      (cnj a * a) * (1 - (cnj b * b) * of_real P)
      + (cnj a * a) * (cnj b * b) * (w + cnj w)
      + (cnj b * b) * (cnj b * b) * of_real P"
    unfolding fid_def rho00_def rho01_def rho10_def rho11_def
    by (simp only: of_real_mult hb[symmetric] of_real_1 algebra_simps)
  show ?thesis
    unfolding step1
    apply (simp only: ha hb hw)
    by (simp only: of_real_mult of_real_add of_real_diff of_real_1 of_real_numeral algebra_simps)
qed

lemma fid_real:
  "Re (fid a b P w) =
     (norm a)\<^sup>2 * (1 - (norm b)\<^sup>2 * P) + (norm b)\<^sup>2 * (norm b)\<^sup>2 * P
       + 2 * (norm a)\<^sup>2 * (norm b)\<^sup>2 * Re w"
  by (simp only: fid_formula Re_complex_of_real)

lemma fid_imag: "Im (fid a b P w) = 0"
  by (simp only: fid_formula Im_complex_of_real)

section \<open>2. Six state average\<close>

definition s2 :: complex where "s2 = of_real (inverse (sqrt 2))"

lemma norm_s2_sq: "(norm s2)\<^sup>2 = 1 / 2"
proof -
  have "norm s2 = inverse (sqrt 2)"
    unfolding s2_def by (simp only: norm_of_real abs_of_nonneg real_sqrt_ge_0_iff inverse_nonnegative_iff_nonnegative)
  hence "(norm s2)\<^sup>2 = inverse ((sqrt 2)\<^sup>2)"
    by (simp only: power_inverse)
  also have "\<dots> = 1 / 2" by (simp only: real_sqrt_pow2 zero_le_numeral inverse_eq_divide)
  finally show ?thesis .
qed

lemma norm_is2_sq: "(norm (\<i> * s2))\<^sup>2 = 1 / 2"
  by (simp only: norm_mult norm_ii mult_1_left norm_s2_sq)

lemma norm_ms2_sq: "(norm (- s2))\<^sup>2 = 1 / 2"
  by (simp only: norm_minus_cancel norm_s2_sq)

lemma norm_mis2_sq: "(norm (- (\<i> * s2)))\<^sup>2 = 1 / 2"
  by (simp only: norm_minus_cancel norm_is2_sq)

text \<open>Fidelity real parts at the six states: ket 0, ket 1, plus and minus, plus i and minus i.\<close>

theorem six_state_average:
  "(Re (fid 1 0 P w) + Re (fid 0 1 P w)
    + Re (fid s2 s2 P w) + Re (fid s2 (- s2) P w)
    + Re (fid s2 (\<i> * s2) P w) + Re (fid s2 (- (\<i> * s2)) P w)) / 6
   = (3 + P + 2 * Re w) / 6"
proof -
  have e1: "Re (fid 1 0 P w) = 1"
    by (simp only: fid_real norm_one norm_zero, simp)
  have e2: "Re (fid 0 1 P w) = P"
    by (simp only: fid_real norm_one norm_zero, simp)
  have e3: "Re (fid s2 s2 P w) = (1 + Re w) / 2"
    by (simp only: fid_real norm_s2_sq, simp add: field_simps)
  have e4: "Re (fid s2 (- s2) P w) = (1 + Re w) / 2"
    by (simp only: fid_real norm_s2_sq norm_ms2_sq, simp add: field_simps)
  have e5: "Re (fid s2 (\<i> * s2) P w) = (1 + Re w) / 2"
    by (simp only: fid_real norm_s2_sq norm_is2_sq, simp add: field_simps)
  have e6: "Re (fid s2 (- (\<i> * s2)) P w) = (1 + Re w) / 2"
    by (simp only: fid_real norm_s2_sq norm_mis2_sq, simp add: field_simps)
  show ?thesis
    by (simp only: e1 e2 e3 e4 e5 e6, simp add: field_simps)
qed

corollary six_state_average_phase:
  assumes "c \<ge> 0"
  shows "(Re (fid 1 0 P (of_real c)) + Re (fid 0 1 P (of_real c))
    + Re (fid s2 s2 P (of_real c)) + Re (fid s2 (- s2) P (of_real c))
    + Re (fid s2 (\<i> * s2) P (of_real c)) + Re (fid s2 (- (\<i> * s2)) P (of_real c))) / 6
   = (3 + P + 2 * c) / 6
   \<and> 1 - (3 + P + 2 * c) / 6 = (1 - P) / 6 + (1 - c) / 3"
proof -
  have "Re (of_real c :: complex) = c" by (simp only: Re_complex_of_real)
  hence h: "(Re (fid 1 0 P (of_real c)) + Re (fid 0 1 P (of_real c))
    + Re (fid s2 s2 P (of_real c)) + Re (fid s2 (- s2) P (of_real c))
    + Re (fid s2 (\<i> * s2) P (of_real c)) + Re (fid s2 (- (\<i> * s2)) P (of_real c))) / 6
    = (3 + P + 2 * Re (of_real c :: complex)) / 6"
    by (rule_tac w = "of_real c" in six_state_average)
  show ?thesis
    using assms h by (simp only: Re_complex_of_real, simp add: field_simps)
qed

section \<open>3. Global fidelity is at most the reduced one\<close>

theorem global_le_reduced:
  fixes P c n :: real
  assumes "n \<ge> P"
  shows "(3 + 2 * P + 2 * c - n) / 6 \<le> (3 + P + 2 * c) / 6"
  using assms by (simp add: field_simps)

section \<open>4. Coherence is at most population\<close>

text \<open>Positive semidefiniteness is stated as: for all complex u and v the quadratic form
conjugate of (u, v) times the matrix times (u, v) has nonnegative real part (the form is real for a Hermitian matrix).
The matrix is: one half, w over 2, conjugate w over 2, P over 2.\<close>

definition psd_form :: "real \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex" where
  "psd_form P w u v =
     cnj u * ((1 / 2) * u + (w / 2) * v) + cnj v * ((cnj w / 2) * u + (of_real P / 2) * v)"

lemma psd_form_real:
  "Re (psd_form P w u v) = ((norm u)\<^sup>2 + P * (norm v)\<^sup>2 + 2 * Re (cnj u * w * v)) / 2"
proof -
  have "psd_form P w u v =
      (cnj u * u + of_real P * (cnj v * v)) / 2 + (cnj u * w * v + cnj (cnj u * w * v)) / 2"
    unfolding psd_form_def by (simp add: field_simps complex_cnj_mult)
  also have "\<dots> =
      (of_real ((norm u)\<^sup>2) + of_real P * of_real ((norm v)\<^sup>2)) / 2
        + of_real (2 * Re (cnj u * w * v)) / 2"
  proof -
    have hu: "cnj u * u = of_real ((norm u)\<^sup>2)"
      by (simp only: mult.commute complex_norm_square)
    have hv: "cnj v * v = of_real ((norm v)\<^sup>2)"
      by (simp only: mult.commute complex_norm_square)
    have hz: "cnj u * w * v + cnj (cnj u * w * v) = of_real (2 * Re (cnj u * w * v))"
      by (simp only: complex_add_cnj of_real_mult of_real_numeral)
    show ?thesis by (simp only: hu hv hz)
  qed
  finally have e: "psd_form P w u v =
      (of_real ((norm u)\<^sup>2) + of_real P * of_real ((norm v)\<^sup>2)) / 2
        + of_real (2 * Re (cnj u * w * v)) / 2" .
  show ?thesis
    by (subst e, simp add: field_simps)
qed

theorem coherence_le_population:
  assumes psd: "\<forall>u v. 0 \<le> Re (psd_form P w u v)"
  shows "(norm w)\<^sup>2 \<le> P"
proof -
  have h: "0 \<le> Re (psd_form P w (- w) 1)" using psd by blast
  have "Re (cnj (- w) * w * 1) = - (norm w)\<^sup>2"
  proof -
    have f: "(norm w)\<^sup>2 = (Re w)\<^sup>2 + (Im w)\<^sup>2" by (rule cmod_power2)
    have g: "Re (cnj (- w) * w * 1) = - (Re w * Re w + Im w * Im w)" by simp
    show ?thesis by (simp only: g, simp only: f, simp only: power2_eq_square)
  qed
  hence "0 \<le> ((norm (- w))\<^sup>2 + P * (norm (1 :: complex))\<^sup>2 + 2 * (- (norm w)\<^sup>2)) / 2"
    using h by (simp only: psd_form_real)
  thus ?thesis by (simp add: field_simps)
qed

corollary coherence_le_population_real:
  fixes c :: real
  assumes "c \<ge> 0" and "\<forall>u v. 0 \<le> Re (psd_form P (of_real c) u v)"
  shows "c\<^sup>2 \<le> P"
proof -
  have "(norm (of_real c :: complex))\<^sup>2 \<le> P"
    by (rule coherence_le_population[OF assms(2)])
  thus ?thesis using assms(1) by (simp add: norm_of_real)
qed

end
