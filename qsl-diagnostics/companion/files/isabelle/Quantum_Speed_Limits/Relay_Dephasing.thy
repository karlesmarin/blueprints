(*  Title:      Relay_Dephasing.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The dephasing excess (2/3) q (1 - q) over the additive budget, and the exact integrals of the optimal
    relay protocol.
*)
theory Relay_Dephasing
  imports "HOL-Analysis.Analysis"
begin

section \<open>The dephasing excess\<close>

text \<open>For 0 <= q <= 1 the quantity q - (2/3) q\<^latex>\<open>\textsuperscript{2}\<close> exceeds the additive budget q/3 by (2/3) q (1 - q), the dephasing excess. It is non-negative on [0, 1] and vanishes only at the two endpoints q = 0 and q = 1.\<close>

theorem dephasing_excess:
  fixes q :: real
  assumes "0 \<le> q" "q \<le> 1"
  shows "q - (2/3) * q\<^sup>2 - q/3 = (2/3) * q * (1 - q)"
    and "(2/3) * q * (1 - q) \<ge> 0"
    and "(2/3) * q * (1 - q) = 0 \<longleftrightarrow> (q = 0 \<or> q = 1)"
proof -
  show "q - (2/3) * q\<^sup>2 - q/3 = (2/3) * q * (1 - q)" by (simp add: power2_eq_square algebra_simps)
  show "(2/3) * q * (1 - q) \<ge> 0" using assms by (intro mult_nonneg_nonneg) auto
  show "(2/3) * q * (1 - q) = 0 \<longleftrightarrow> (q = 0 \<or> q = 1)" by auto
qed

section \<open>Exact integrals of the optimal protocol\<close>

text \<open>Exact values of four definite integrals over [0, pi] of integrands built from ((1 + cos theta) / 2)\<^latex>\<open>\textsuperscript{2}\<close> and (sin theta)\<^latex>\<open>\textsuperscript{2}\<close> / 2, the two angular profiles of the optimal relay protocol: 3 pi / 8 and pi / 4, and the corresponding integrals of q - (2/3) q\<^latex>\<open>\textsuperscript{2}\<close>, which are 37/24 * 1/3 * (3 pi / 8) and 9/4 * 1/3 * (pi / 4).\<close>

lemma ftc_real:
  fixes F f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "\<And>x. (F has_real_derivative f x) (at x)"
  shows "(f has_integral F b - F a) {a..b}"
proof (rule fundamental_theorem_of_calculus[OF assms(1)])
  fix x assume "x \<in> {a..b}"
  show "(F has_vector_derivative f x) (at x within {a..b})"
    using assms(2)[of x] by (simp add: has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within)
qed

lemma sc2: "sin x ^ 2 = 1 - cos x ^ 2" for x :: real
  by (simp add: sin_squared_eq)

theorem optimal_protocol_integrals:
  shows "integral {0..pi} (\<lambda>\<theta>. ((1 + cos \<theta>) / 2)\<^sup>2) = 3 * pi / 8"
    and "integral {0..pi} (\<lambda>\<theta>. (sin \<theta>)\<^sup>2 / 2) = pi / 4"
    and "integral {0..pi} (\<lambda>\<theta>. ((1 + cos \<theta>) / 2)\<^sup>2 - (2/3) * ((1 + cos \<theta>) / 2) ^ 4)
          = (37/24) * (1/3) * (3 * pi / 8)"
    and "integral {0..pi} (\<lambda>\<theta>. (sin \<theta>)\<^sup>2 / 2 - (2/3) * ((sin \<theta>)\<^sup>2 / 2)\<^sup>2)
          = (9/4) * (1/3) * (pi / 4)"
proof -
  have I1: "((\<lambda>\<theta>. ((1 + cos \<theta>) / 2)\<^sup>2) has_integral 3 * pi / 8) {0..pi}"
  proof -
    let ?F = "\<lambda>x::real. 3 * x / 8 + sin x * cos x / 8 + sin x / 2"
    have "((\<lambda>\<theta>. ((1 + cos \<theta>) / 2)\<^sup>2) has_integral ?F pi - ?F 0) {0..pi}"
    proof (rule ftc_real[OF pi_ge_zero])
      fix x :: real
      have "(?F has_real_derivative (3/8 + (cos x * cos x - sin x * sin x) / 8 + cos x / 2)) (at x)"
        by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square power3_eq_cube)
      moreover have "3/8 + (cos x * cos x - sin x * sin x) / 8 + cos x / 2 = ((1 + cos x) / 2)\<^sup>2"
        by (simp add: field_simps) (use sin_cos_squared_add[of x] in algebra)
      ultimately show "(?F has_real_derivative ((1 + cos x) / 2)\<^sup>2) (at x)" by simp
    qed
    thus ?thesis by simp
  qed
  have I2: "((\<lambda>\<theta>. (sin \<theta>)\<^sup>2 / 2) has_integral pi / 4) {0..pi}"
  proof -
    let ?F = "\<lambda>x::real. x / 4 - sin x * cos x / 4"
    have "((\<lambda>\<theta>. (sin \<theta>)\<^sup>2 / 2) has_integral ?F pi - ?F 0) {0..pi}"
    proof (rule ftc_real[OF pi_ge_zero])
      fix x :: real
      have "(?F has_real_derivative (1/4 - (cos x * cos x - sin x * sin x) / 4)) (at x)"
        by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square power3_eq_cube)
      moreover have "1/4 - (cos x * cos x - sin x * sin x) / 4 = (sin x)\<^sup>2 / 2"
        by (simp add: field_simps) (use sin_cos_squared_add[of x] in algebra)
      ultimately show "(?F has_real_derivative (sin x)\<^sup>2 / 2) (at x)" by simp
    qed
    thus ?thesis by simp
  qed
  have I3: "((\<lambda>\<theta>. ((1 + cos \<theta>) / 2)\<^sup>2 - (2/3) * ((1 + cos \<theta>) / 2) ^ 4) has_integral 37 * pi / 192) {0..pi}"
  proof -
    let ?F = "\<lambda>x::real. 37 * x / 192 + (sin x) ^ 3 / 18 - sin x * (cos x) ^ 3 / 96 - sin x * cos x / 64 + sin x / 6"
    have "((\<lambda>\<theta>. ((1 + cos \<theta>) / 2)\<^sup>2 - (2/3) * ((1 + cos \<theta>) / 2) ^ 4) has_integral ?F pi - ?F 0) {0..pi}"
    proof (rule ftc_real[OF pi_ge_zero])
      fix x :: real
      have "(?F has_real_derivative (37/192 + 3 * (sin x)^2 * cos x / 18
          - (cos x * (cos x)^3 + sin x * (3 * (cos x)^2 * (- sin x))) / 96
          - (cos x * cos x - sin x * sin x) / 64 + cos x / 6)) (at x)"
        by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square power3_eq_cube)
      moreover have "37/192 + 3 * (sin x)^2 * cos x / 18
          - (cos x * (cos x)^3 + sin x * (3 * (cos x)^2 * (- sin x))) / 96
          - (cos x * cos x - sin x * sin x) / 64 + cos x / 6
          = ((1 + cos x) / 2)\<^sup>2 - (2/3) * ((1 + cos x) / 2) ^ 4"
        by (simp add: field_simps) (use sin_cos_squared_add[of x] in algebra)
      ultimately show "(?F has_real_derivative ((1 + cos x) / 2)\<^sup>2 - (2/3) * ((1 + cos x) / 2) ^ 4) (at x)" by simp
    qed
    thus ?thesis by simp
  qed
  have I4: "((\<lambda>\<theta>. (sin \<theta>)\<^sup>2 / 2 - (2/3) * ((sin \<theta>)\<^sup>2 / 2)\<^sup>2) has_integral 3 * pi / 16) {0..pi}"
  proof -
    let ?F = "\<lambda>x::real. 3 * x / 16 + (sin x) ^ 3 * cos x / 24 - 3 * sin x * cos x / 16"
    have "((\<lambda>\<theta>. (sin \<theta>)\<^sup>2 / 2 - (2/3) * ((sin \<theta>)\<^sup>2 / 2)\<^sup>2) has_integral ?F pi - ?F 0) {0..pi}"
    proof (rule ftc_real[OF pi_ge_zero])
      fix x :: real
      have "(?F has_real_derivative (3/16 + (3 * (sin x)^2 * cos x * cos x + (sin x)^3 * (- sin x)) / 24
          - 3 * (cos x * cos x - sin x * sin x) / 16)) (at x)"
        by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square power3_eq_cube)
      moreover have "3/16 + (3 * (sin x)^2 * cos x * cos x + (sin x)^3 * (- sin x)) / 24
          - 3 * (cos x * cos x - sin x * sin x) / 16
          = (sin x)\<^sup>2 / 2 - (2/3) * ((sin x)\<^sup>2 / 2)\<^sup>2"
        by (simp add: field_simps) (use sin_cos_squared_add[of x] in algebra)
      ultimately show "(?F has_real_derivative (sin x)\<^sup>2 / 2 - (2/3) * ((sin x)\<^sup>2 / 2)\<^sup>2) (at x)" by simp
    qed
    thus ?thesis by simp
  qed
  show "integral {0..pi} (\<lambda>\<theta>. ((1 + cos \<theta>) / 2)\<^sup>2) = 3 * pi / 8" using I1 by (rule integral_unique)
  show "integral {0..pi} (\<lambda>\<theta>. (sin \<theta>)\<^sup>2 / 2) = pi / 4" using I2 by (rule integral_unique)
  show "integral {0..pi} (\<lambda>\<theta>. ((1 + cos \<theta>) / 2)\<^sup>2 - (2/3) * ((1 + cos \<theta>) / 2) ^ 4)
          = (37/24) * (1/3) * (3 * pi / 8)"
    using I3 by (simp add: integral_unique)
  show "integral {0..pi} (\<lambda>\<theta>. (sin \<theta>)\<^sup>2 / 2 - (2/3) * ((sin \<theta>)\<^sup>2 / 2)\<^sup>2)
          = (9/4) * (1/3) * (pi / 4)"
    using I4 by (simp add: integral_unique)
qed

end
