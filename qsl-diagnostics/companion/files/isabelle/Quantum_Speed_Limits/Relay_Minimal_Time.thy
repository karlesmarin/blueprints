(*  Title:      Relay_Minimal_Time.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Minimal transfer time of the qubit--bus--qubit relay with bounded couplings: G T >= pi / sqrt 2,
    proved with the calibration function Phi.
*)
theory Relay_Minimal_Time
  imports "HOL-Analysis.Analysis"
begin

text \<open>A qubit A is coupled to a bus mode, and the bus mode to a qubit B. The couplings are bounded, in modulus, by G. Writing x for the modulus of the amplitude of qubit A, z for that of qubit B, the remaining weight 1 - x\<^latex>\<open>\textsuperscript{2}\<close> - z\<^latex>\<open>\textsuperscript{2}\<close> is the occupation of the bus, and the coupling bound reads |x'|, |z'| <= G sqrt (1 - x\<^latex>\<open>\textsuperscript{2}\<close> - z\<^latex>\<open>\textsuperscript{2}\<close>). We show that transferring the excitation from A to B (x = 1 at time 0, z = 1 at time T) needs G T >= pi / sqrt 2, by means of a calibration function Phi of the pair (x, z).\<close>

section \<open>Algebraic bounds\<close>

lemma D1_bound:
  fixes x z x1 z1 G y :: real
  assumes "0 \<le> x" "0 \<le> z" "x + z \<le> 1" "0 < y" "y^2 = 1 - x^2 - z^2"
    and "\<bar>x1\<bar> \<le> G * y" "\<bar>z1\<bar> \<le> G * y"
  shows "\<bar>((x1 - z1) + (x - z) * (x + z) * (x1 + z1) / (2 - (x + z)^2)) / (2 * y)\<bar> \<le> G"
proof -
  define s where "s = x + z"
  define d where "d = x - z"
  have sd: "s^2 + d^2 = 2 * x^2 + 2 * z^2" by (simp add: s_def d_def power2_eq_square algebra_simps)
  have s0: "0 \<le> s" and s1: "s^2 \<le> 1" using assms unfolding s_def by (auto intro: power_le_one)
  have h2: "0 < 2 - s^2" using s1 by simp
  have dd: "d^2 \<le> 2 - s^2" using sd assms(5) zero_le_power2[of y] by linarith
  have "(d * s)^2 \<le> (2 - s^2)^2"
  proof -
    have "(d * s)^2 = d^2 * s^2" by (simp add: power_mult_distrib)
    also have "... \<le> (2 - s^2) * s^2" using dd by (intro mult_right_mono) auto
    also have "... \<le> (2 - s^2) * (2 - s^2)" using h2 s1 by (intro mult_left_mono) auto
    finally show ?thesis by (simp add: power2_eq_square)
  qed
  hence "\<bar>d * s\<bar> \<le> \<bar>2 - s^2\<bar>" by (rule iffD2[OF abs_le_square_iff])
  hence "\<bar>d * s\<bar> \<le> 2 - s^2" using h2 by simp
  hence \<kappa>0: "\<bar>d * s\<bar> \<le> 2 - s^2" .
  define k where "k = d * s / (2 - s^2)"
  have \<kappa>: "\<bar>k\<bar> \<le> 1"
  proof -
    have "\<bar>k\<bar> = \<bar>d * s\<bar> / (2 - s^2)" unfolding k_def using h2 by (simp add: abs_divide)
    also have "... \<le> 1" using \<kappa>0 h2 by (simp add: divide_le_eq_1_pos)
    finally show ?thesis .
  qed
  have N: "(x1 - z1) + d * s * (x1 + z1) / (2 - s^2) = (1 + k) * x1 - (1 - k) * z1"
    by (simp add: k_def field_simps) (simp only: add_divide_distrib)
  have k1: "0 \<le> 1 + k" and k2: "0 \<le> 1 - k" using \<kappa> by (auto simp: abs_le_iff)
  have "\<bar>(1 + k) * x1 - (1 - k) * z1\<bar> \<le> (1 + k) * \<bar>x1\<bar> + (1 - k) * \<bar>z1\<bar>"
    using k1 k2 by (auto simp: abs_mult intro: order_trans[OF abs_triangle_ineq4])
  also have "... \<le> (1 + k) * (G * y) + (1 - k) * (G * y)"
    using k1 k2 assms by (intro add_mono mult_left_mono) auto
  also have "... = 2 * (G * y)" by (simp add: algebra_simps)
  finally have "\<bar>(1 + k) * x1 - (1 - k) * z1\<bar> \<le> 2 * (G * y)" .
  hence "\<bar>(1 + k) * x1 - (1 - k) * z1\<bar> / (2 * y) \<le> G" using assms(4) by (simp add: divide_le_eq)
  thus ?thesis using N assms(4) unfolding s_def d_def by (simp add: abs_divide)
qed

lemma sq_prod: "0 \<le> c \<Longrightarrow> (sqrt 2 * sqrt c)^2 = 2 * (c::real)"
proof -
  assume c: "0 \<le> c"
  have "(sqrt 2 * sqrt c)^2 = (sqrt 2)^2 * (sqrt c)^2" by (rule power_mult_distrib)
  also have "(sqrt 2)^2 = (2::real)" by (rule real_sqrt_pow2) simp
  also have "(sqrt c)^2 = c" by (rule real_sqrt_pow2[OF c])
  finally show ?thesis .
qed

lemma div_bound:
  fixes a b q G y :: real
  assumes q0: "0 < q" and yq: "2 * y \<le> q" and G: "0 \<le> G" and ha: "\<bar>a\<bar> \<le> G * y" and hb: "\<bar>b\<bar> \<le> G * y"
  shows "\<bar>(a - b) / q\<bar> \<le> G"
proof -
  have "\<bar>a - b\<bar> \<le> \<bar>a\<bar> + \<bar>b\<bar>" by (rule abs_triangle_ineq4)
  also have "... \<le> 2 * (G * y)" using ha hb by linarith
  also have "... = G * (2 * y)" by (simp add: algebra_simps)
  also have "... \<le> G * q" by (rule mult_left_mono[OF yq G])
  finally have "\<bar>a - b\<bar> \<le> G * q" .
  hence "\<bar>a - b\<bar> / q \<le> G" using q0 by (simp add: divide_le_eq)
  thus ?thesis using q0 by (simp add: abs_divide)
qed

lemma D2_bound:
  fixes x z x1 z1 G y :: real
  assumes "0 \<le> y" "y^2 = 1 - x^2 - z^2" "(x - z)^2 < 1" "1 \<le> (x + z)^2" "0 \<le> G"
    and "\<bar>x1\<bar> \<le> G * y" "\<bar>z1\<bar> \<le> G * y"
  shows "\<bar>(x1 - z1) / (sqrt 2 * sqrt (1 - (x - z)^2))\<bar> \<le> G"
proof -
  define q where "q = sqrt 2 * sqrt (1 - (x - z)^2)"
  have hn: "0 < 1 - (x - z)^2" using assms(3) by simp
  have q0: "0 < q" unfolding q_def using hn by (simp add: real_sqrt_gt_0_iff)
  have q2: "q^2 = 2 * (1 - (x - z)^2)" unfolding q_def by (rule sq_prod) (use hn in simp)
  have e4: "(2 * y)^2 = 4 * y^2" by (simp add: power_mult_distrib)
  have key: "q^2 - (2 * y)^2 = 2 * ((x + z)^2 - 1)"
  proof -
    have "q^2 - (2 * y)^2 = 2 * (1 - (x - z)^2) - 4 * y^2" using q2 e4 by simp
    also have "... = 2 * (1 - (x - z)^2) - 4 * (1 - x^2 - z^2)" using assms(2) by simp
    also have "... = 2 * ((x + z)^2 - 1)" by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  have "0 \<le> q^2 - (2 * y)^2" unfolding key using assms(4) by simp
  hence "(2 * y)^2 \<le> q^2" by simp
  hence yq: "2 * y \<le> q" by (rule power2_le_imp_le) (use q0 in simp)
  show ?thesis unfolding q_def[symmetric] by (rule div_bound[OF q0 yq assms(5) assms(6) assms(7)])
qed


section \<open>A squeeze lemma for derivatives\<close>

lemma squeeze_deriv:
  fixes fa fb g :: "real \<Rightarrow> real"
  assumes d1: "(fa has_real_derivative c) (at t)" and d2: "(fb has_real_derivative c) (at t)"
    and e: "fa t = fb t" "g t = fa t" and c: "\<And>u. g u = fa u \<or> g u = fb u"
  shows "(g has_real_derivative c) (at t)"
proof -
  have q1: "((\<lambda>y. (fa y - fa t) / (y - t)) \<longlongrightarrow> c) (at t)" using d1 by (simp add: has_field_derivative_iff)
  have q2: "((\<lambda>y. (fb y - fb t) / (y - t)) \<longlongrightarrow> c) (at t)" using d2 by (simp add: has_field_derivative_iff)
  have "((\<lambda>y. (g y - g t) / (y - t)) \<longlongrightarrow> c) (at t)"
  proof (rule tendstoI)
    fix \<epsilon> :: real assume \<epsilon>: "0 < \<epsilon>"
    have "eventually (\<lambda>y. dist ((fa y - fa t) / (y - t)) c < \<epsilon> \<and> dist ((fb y - fb t) / (y - t)) c < \<epsilon>) (at t)"
      using tendstoD[OF q1 \<epsilon>] tendstoD[OF q2 \<epsilon>] by (rule eventually_conj)
    thus "eventually (\<lambda>y. dist ((g y - g t) / (y - t)) c < \<epsilon>) (at t)"
    proof (rule eventually_mono)
      fix y assume "dist ((fa y - fa t) / (y - t)) c < \<epsilon> \<and> dist ((fb y - fb t) / (y - t)) c < \<epsilon>"
      thus "dist ((g y - g t) / (y - t)) c < \<epsilon>" using c[of y] e by auto
    qed
  qed
  thus ?thesis by (simp add: has_field_derivative_iff)
qed

section \<open>Derivatives of the two branches\<close>

lemma deriv_branch2:
  fixes x z :: "real \<Rightarrow> real"
  assumes hx: "(x has_real_derivative x1) (at t)" and hz: "(z has_real_derivative z1) (at t)"
    and hd: "(x t - z t)^2 < 1"
  shows "((\<lambda>u. arcsin (x u - z u) / sqrt 2) has_real_derivative
      (x1 - z1) / (sqrt 2 * sqrt (1 - (x t - z t)^2))) (at t)"
proof -
  have h1: "((\<lambda>u. x u - z u) has_real_derivative (x1 - z1)) (at t)" using hx hz by (rule DERIV_diff)
  have b1: "x t - z t < 1" using power2_less_imp_less[of "x t - z t" 1] hd by simp
  have b2: "-1 < x t - z t" using power2_less_imp_less[of "z t - x t" 1] hd
    by (simp add: power2_commute)
  have "((\<lambda>u. arcsin (x u - z u)) has_real_derivative inverse (sqrt (1 - (x t - z t)^2)) * (x1 - z1)) (at t)"
    using DERIV_chain2[OF DERIV_arcsin[OF b2 b1] h1] by (simp add: o_def)
  hence "((\<lambda>u. arcsin (x u - z u) / sqrt 2) has_real_derivative
      inverse (sqrt (1 - (x t - z t)^2)) * (x1 - z1) / sqrt 2) (at t)"
    by (rule DERIV_cdivide)
  moreover have "inverse (sqrt (1 - (x t - z t)^2)) * (x1 - z1) / sqrt 2
      = (x1 - z1) / (sqrt 2 * sqrt (1 - (x t - z t)^2))"
    by (simp add: field_simps)
  ultimately show ?thesis by simp
qed

lemma alg_id:
  fixes a b d s r y q :: real
  assumes "r \<noteq> 0" "y \<noteq> 0" "q \<noteq> 0"
  shows "inverse (q * y / r) * (((a) * r - d * (inverse r / 2 * (- (2 * s * b)))) / r^2) / q
      = (a + d * s * b / r^2) / (q * q * y)"
  using assms by (simp add: field_simps power2_eq_square)


lemma deriv_branch1:
  fixes x z :: "real \<Rightarrow> real"
  assumes hx: "(x has_real_derivative x1) (at t)" and hz: "(z has_real_derivative z1) (at t)"
    and hy: "0 < 1 - (x t)^2 - (z t)^2"
  shows "((\<lambda>u. arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2) has_real_derivative
     (((x1 - z1) + (x t - z t) * (x t + z t) * (x1 + z1) / (2 - (x t + z t)^2))
        / (2 * sqrt (1 - (x t)^2 - (z t)^2)))) (at t)"
proof -
  define s where "s = x t + z t"
  define d where "d = x t - z t"
  define y where "y = sqrt (1 - (x t)^2 - (z t)^2)"
  have sd: "s^2 + d^2 = 2 * (x t)^2 + 2 * (z t)^2" by (simp add: s_def d_def power2_eq_square algebra_simps)
  have y0: "0 < y" unfolding y_def using hy by simp
  have y2: "y^2 = 1 - (x t)^2 - (z t)^2" unfolding y_def using hy by simp
  have hs2: "0 < 2 - s^2"
  proof -
    have "0 < y^2" using y0 by simp
    moreover have "0 \<le> d^2" by simp
    ultimately show ?thesis using sd y2 by linarith
  qed
  define r where "r = sqrt (2 - s^2)"
  have r0: "0 < r" unfolding r_def using hs2 by simp
  have r2: "r^2 = 2 - s^2" unfolding r_def using hs2 by simp
  have rd: "r^2 - d^2 = 2 * y^2" using r2 sd y2 by simp
  have du: "d^2 < r^2" using rd y0 by (simp add: field_simps)
  have u1: "d / r < 1" and u2: "-1 < d / r"
  proof -
    have "(d / r)^2 < 1" using du r0 by (simp add: power_divide divide_less_eq_1_pos)
    thus "d / r < 1" "-1 < d / r"
      using power2_less_imp_less[of "d / r" 1] power2_less_imp_less[of "- (d / r)" 1] by simp_all
  qed
  have hw: "((\<lambda>u. 2 - (x u + z u)^2) has_real_derivative (- (2 * s * (x1 + z1)))) (at t)"
    using hx hz by (auto intro!: derivative_eq_intros simp: s_def)
  have hr: "((\<lambda>u. sqrt (2 - (x u + z u)^2)) has_real_derivative (inverse r / 2 * (- (2 * s * (x1 + z1))))) (at t)"
    using DERIV_chain2[OF DERIV_real_sqrt[OF hs2[unfolded s_def]] hw[unfolded s_def]]
    by (simp add: s_def r_def o_def)
  have hX: "((\<lambda>u. x u - z u) has_real_derivative (x1 - z1)) (at t)" using hx hz by (rule DERIV_diff)
  have hU: "((\<lambda>u. (x u - z u) / sqrt (2 - (x u + z u)^2)) has_real_derivative
      (((x1 - z1) * r - d * (inverse r / 2 * (- (2 * s * (x1 + z1))))) / r^2)) (at t)"
    using DERIV_divide[OF hX hr] r0 by (simp add: r_def d_def s_def)
  have hA: "((\<lambda>u. arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2))) has_real_derivative
      (inverse (sqrt (1 - (d / r)^2)) * (((x1 - z1) * r - d * (inverse r / 2 * (- (2 * s * (x1 + z1))))) / r^2))) (at t)"
  proof -
    have e: "d / r = (x t - z t) / sqrt (2 - (x t + z t)^2)" by (simp add: d_def r_def s_def)
    have Darc: "(arcsin has_real_derivative inverse (sqrt (1 - (d / r)^2))) (at ((x t - z t) / sqrt (2 - (x t + z t)^2)))"
      using DERIV_arcsin[OF u2 u1] unfolding e .
    show ?thesis using DERIV_chain2[OF Darc hU] by (simp add: o_def)
  qed
  have hB: "((\<lambda>u. arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2) has_real_derivative
      (inverse (sqrt (1 - (d / r)^2)) * (((x1 - z1) * r - d * (inverse r / 2 * (- (2 * s * (x1 + z1))))) / r^2)) / sqrt 2) (at t)"
    by (rule DERIV_cdivide[OF hA])
  have sq: "sqrt (1 - (d / r)^2) = sqrt 2 * y / r"
  proof -
    have "1 - (d / r)^2 = (r^2 - d^2) / r^2"
    proof -
      have "(r^2 - d^2) / r^2 = r^2 / r^2 - d^2 / r^2" by (rule diff_divide_distrib)
      also have "r^2 / r^2 = 1" using r0 by simp
      finally show ?thesis by (simp add: power_divide)
    qed
    also have "... = 2 * y^2 / r^2" using rd by simp
    also have "... = (sqrt 2 * y / r)^2" by (simp add: power_divide power_mult_distrib)
    finally have h1: "1 - (d / r)^2 = (sqrt 2 * y / r)^2" .
    have h2: "0 \<le> sqrt 2 * y / r" using y0 r0 by simp
    show ?thesis by (rule real_sqrt_unique[OF h1[symmetric] h2])
  qed
  have s22: "sqrt 2 * sqrt 2 = (2::real)" by simp
  have "(inverse (sqrt (1 - (d / r)^2)) * (((x1 - z1) * r - d * (inverse r / 2 * (- (2 * s * (x1 + z1))))) / r^2)) / sqrt 2
      = ((x1 - z1) + d * s * (x1 + z1) / r^2) / (sqrt 2 * sqrt 2 * y)"
    unfolding sq by (rule alg_id) (use r0 y0 in simp_all)
  also have "... = ((x1 - z1) + d * s * (x1 + z1) / (2 - s^2)) / (2 * y)"
    unfolding s22 r2 ..
  finally show ?thesis using hB unfolding s_def d_def y_def by simp
qed



section \<open>The calibration function\<close>

text \<open>Phi a b is arcsin ((a - b) / sqrt (2 - (a + b)\<^latex>\<open>\textsuperscript{2}\<close>)) / sqrt 2 while a + b <= 1, and arcsin (a - b) / sqrt 2 beyond; it equals pi / (2 sqrt 2) at the start (a, b) = (1, 0) and its negative at the target (0, 1).\<close>

definition Phi :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Phi a b = (if a + b \<le> 1 then arcsin ((a - b) / sqrt (2 - (a + b)^2)) / sqrt 2
              else arcsin (a - b) / sqrt 2)"

lemma nn_from_abs: fixes a G :: real shows "\<bar>a\<bar> \<le> G \<Longrightarrow> 0 \<le> G + a"
  by (auto simp: abs_le_iff)

lemma sq_lt1: "0 \<le> s \<Longrightarrow> s < 1 \<Longrightarrow> s^2 < (1::real)"
  using power_strict_mono[of s 1 2] by simp

lemma sq_gt1: "1 < s \<Longrightarrow> 1 < s^2" for s :: real
  using power_strict_mono[of 1 s 2] by simp

lemma key_deriv:
  fixes x z :: "real \<Rightarrow> real" and G x1 z1 :: real
  assumes G: "0 \<le> G"
    and hx: "(x has_real_derivative x1) (at t)" and hz: "(z has_real_derivative z1) (at t)"
    and x0: "0 \<le> x t" and z0: "0 \<le> z t" and D: "(x t)^2 + (z t)^2 \<le> 1" and xn: "x t \<noteq> 1" and zn: "z t \<noteq> 1"
    and bx: "\<bar>x1\<bar> \<le> G * sqrt (1 - (x t)^2 - (z t)^2)" and bz: "\<bar>z1\<bar> \<le> G * sqrt (1 - (x t)^2 - (z t)^2)"
    and hs: "x t + z t = 1 \<Longrightarrow> x1 + z1 = 0"
  shows "\<exists>c. 0 \<le> c \<and> ((\<lambda>u. G * u + Phi (x u) (z u)) has_real_derivative c) (at t)"
proof -
  define y where "y = sqrt (1 - (x t)^2 - (z t)^2)"
  have hD: "0 \<le> 1 - (x t)^2 - (z t)^2" using D by linarith
  have y0: "0 \<le> y" unfolding y_def by (rule real_sqrt_ge_zero[OF hD])
  have y2: "y^2 = 1 - (x t)^2 - (z t)^2" unfolding y_def by (rule real_sqrt_pow2[OF hD])
  have xz0: "0 \<le> x t * z t" using x0 z0 by simp
  have sexp: "(x t + z t)^2 = (x t)^2 + (z t)^2 + 2 * (x t * z t)" by (simp add: power2_eq_square algebra_simps)
  have dexp: "(x t - z t)^2 = (x t)^2 + (z t)^2 - 2 * (x t * z t)" by (simp add: power2_eq_square algebra_simps)
  have cs: "isCont (\<lambda>u. x u + z u) t" using hx hz by (intro isCont_add DERIV_isCont)
  have csn: "((\<lambda>u. x u + z u) \<longlongrightarrow> x t + z t) (nhds t)"
    using tendsto_at_iff_tendsto_nhds[of "\<lambda>u. x u + z u" t] cs unfolding isCont_def by simp
  have hG: "((\<lambda>u. G * u) has_real_derivative G) (at t)" by (auto intro!: derivative_eq_intros)
  consider "x t + z t < 1" | "x t + z t = 1" | "1 < x t + z t" by linarith
  then show ?thesis
  proof cases
    case 1
    have s0: "0 \<le> x t + z t" using x0 z0 by simp
    have s1: "(x t + z t)^2 < 1" by (rule sq_lt1[OF s0 1])
    have hy: "0 < 1 - (x t)^2 - (z t)^2"
      using s1 sexp xz0 by linarith
    have yp: "0 < y" using hy unfolding y_def by simp
    have dv: "((\<lambda>u. arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2) has_real_derivative
        (((x1 - z1) + (x t - z t) * (x t + z t) * (x1 + z1) / (2 - (x t + z t)^2)) / (2 * y))) (at t)"
      unfolding y_def by (rule deriv_branch1[OF hx hz hy])
    have bd: "\<bar>((x1 - z1) + (x t - z t) * (x t + z t) * (x1 + z1) / (2 - (x t + z t)^2)) / (2 * y)\<bar> \<le> G"
      using D1_bound[OF x0 z0 _ yp y2] 1 bx bz unfolding y_def by simp
    have ev: "eventually (\<lambda>u. x u + z u < 1) (nhds t)"
      using order_tendstoD(2)[OF csn 1] .
    have X1: "((\<lambda>u. G * u + arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2) has_real_derivative
        G + (((x1 - z1) + (x t - z t) * (x t + z t) * (x1 + z1) / (2 - (x t + z t)^2)) / (2 * y))) (at t)"
      by (rule DERIV_add[OF hG dv])
    have "((\<lambda>u. G * u + Phi (x u) (z u)) has_real_derivative
        G + (((x1 - z1) + (x t - z t) * (x t + z t) * (x1 + z1) / (2 - (x t + z t)^2)) / (2 * y))) (at t)"
      by (rule iffD1[OF DERIV_cong_ev[OF refl _ refl] X1]) (rule eventually_mono[OF ev], simp add: Phi_def)
    moreover have "0 \<le> G + (((x1 - z1) + (x t - z t) * (x t + z t) * (x1 + z1) / (2 - (x t + z t)^2)) / (2 * y))"
      by (rule nn_from_abs[OF bd])
    ultimately show ?thesis by blast
  next
    case 3
    have s2: "1 < (x t + z t)^2" by (rule sq_gt1[OF 3])
    have xzp: "0 < x t * z t" using s2 sexp D by linarith
    have hd: "(x t - z t)^2 < 1" using dexp D xzp by linarith
    have dv: "((\<lambda>u. arcsin (x u - z u) / sqrt 2) has_real_derivative
        (x1 - z1) / (sqrt 2 * sqrt (1 - (x t - z t)^2))) (at t)" by (rule deriv_branch2[OF hx hz hd])
    have bd: "\<bar>(x1 - z1) / (sqrt 2 * sqrt (1 - (x t - z t)^2))\<bar> \<le> G"
      using D2_bound[OF y0 y2 hd _ G] s2 bx bz unfolding y_def by simp
    have ev: "eventually (\<lambda>u. 1 < x u + z u) (nhds t)"
      using order_tendstoD(1)[OF csn 3] .
    have X2: "((\<lambda>u. G * u + arcsin (x u - z u) / sqrt 2) has_real_derivative
        G + (x1 - z1) / (sqrt 2 * sqrt (1 - (x t - z t)^2))) (at t)" by (rule DERIV_add[OF hG dv])
    have "((\<lambda>u. G * u + Phi (x u) (z u)) has_real_derivative
        G + (x1 - z1) / (sqrt 2 * sqrt (1 - (x t - z t)^2))) (at t)"
      by (rule iffD1[OF DERIV_cong_ev[OF refl _ refl] X2]) (rule eventually_mono[OF ev], simp add: Phi_def)
    moreover have "0 \<le> G + (x1 - z1) / (sqrt 2 * sqrt (1 - (x t - z t)^2))"
      by (rule nn_from_abs[OF bd])
    ultimately show ?thesis by blast
  next
    case 2
    have xzy: "x t * z t = y^2 / 2" using sexp 2 y2 by simp
    have yp: "0 < y"
    proof (rule ccontr)
      assume "\<not> 0 < y"
      with y0 have "y = 0" by simp
      hence "x t * z t = 0" using xzy by simp
      hence "x t = 0 \<or> z t = 0" by simp
      thus False using 2 xn zn by auto
    qed
    have d2: "(x t - z t)^2 = 1 - 2 * y^2" using dexp xzy y2 by linarith
    have hd: "(x t - z t)^2 < 1" using d2 yp by simp
    have s1: "x1 + z1 = 0" by (rule hs[OF 2])
    have sq: "sqrt (1 - (x t - z t)^2) = sqrt 2 * y"
    proof -
      have "1 - (x t - z t)^2 = (sqrt 2 * y)^2" using d2 by (simp add: power_mult_distrib)
      moreover have "0 \<le> sqrt 2 * y" using y0 by simp
      ultimately show ?thesis by (simp add: real_sqrt_abs)
    qed
    have dv1: "((\<lambda>u. arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2) has_real_derivative
        ((x1 - z1) / (2 * y))) (at t)"
    proof -
      have yy: "0 < y^2" using yp by simp
      have hy: "0 < 1 - (x t)^2 - (z t)^2" using y2 yy by linarith
      have "((\<lambda>u. arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2) has_real_derivative
        (((x1 - z1) + (x t - z t) * (x t + z t) * (x1 + z1) / (2 - (x t + z t)^2)) / (2 * y))) (at t)"
        unfolding y_def by (rule deriv_branch1[OF hx hz hy])
      thus ?thesis using s1 by simp
    qed
    have dv2: "((\<lambda>u. arcsin (x u - z u) / sqrt 2) has_real_derivative ((x1 - z1) / (2 * y))) (at t)"
    proof -
      have "((\<lambda>u. arcsin (x u - z u) / sqrt 2) has_real_derivative
        (x1 - z1) / (sqrt 2 * sqrt (1 - (x t - z t)^2))) (at t)" by (rule deriv_branch2[OF hx hz hd])
      moreover have "sqrt 2 * sqrt (1 - (x t - z t)^2) = 2 * y"
        unfolding sq by (simp add: mult.assoc[symmetric])
      ultimately show ?thesis by simp
    qed
    have bd: "\<bar>(x1 - z1) / (2 * y)\<bar> \<le> G"
    proof -
      have "\<bar>((x1 - z1) + (x t - z t) * (x t + z t) * (x1 + z1) / (2 - (x t + z t)^2)) / (2 * y)\<bar> \<le> G"
        using D1_bound[OF x0 z0 _ yp y2] 2 bx bz unfolding y_def by simp
      thus ?thesis using s1 by simp
    qed
    have f12: "G * t + arcsin ((x t - z t) / sqrt (2 - (x t + z t)^2)) / sqrt 2 = G * t + arcsin (x t - z t) / sqrt 2"
      using 2 by simp
    have "((\<lambda>u. G * u + Phi (x u) (z u)) has_real_derivative G + (x1 - z1) / (2 * y)) (at t)"
    proof (rule squeeze_deriv[where fa = "\<lambda>u. G * u + arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2"
        and fb = "\<lambda>u. G * u + arcsin (x u - z u) / sqrt 2"])
      show "((\<lambda>u. G * u + arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2) has_real_derivative
          G + (x1 - z1) / (2 * y)) (at t)" by (rule DERIV_add[OF hG dv1])
      show "((\<lambda>u. G * u + arcsin (x u - z u) / sqrt 2) has_real_derivative
          G + (x1 - z1) / (2 * y)) (at t)" by (rule DERIV_add[OF hG dv2])
      show "G * t + arcsin ((x t - z t) / sqrt (2 - (x t + z t)^2)) / sqrt 2 = G * t + arcsin (x t - z t) / sqrt 2"
        by (rule f12)
      show "G * t + Phi (x t) (z t) = G * t + arcsin ((x t - z t) / sqrt (2 - (x t + z t)^2)) / sqrt 2"
        using 2 by (simp add: Phi_def)
      show "\<And>u. G * u + Phi (x u) (z u) = G * u + arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2
          \<or> G * u + Phi (x u) (z u) = G * u + arcsin (x u - z u) / sqrt 2"
        by (simp add: Phi_def)
    qed
    moreover have "0 \<le> G + (x1 - z1) / (2 * y)" by (rule nn_from_abs[OF bd])
    ultimately show ?thesis by blast
  qed
qed

section \<open>Continuity of Phi and a countability lemma\<close>

lemma abs_le1: "a^2 \<le> (1::real) \<Longrightarrow> a \<in> {-1..1}"
  using abs_le_square_iff[of a 1] by (auto simp: abs_le_iff)

lemma cont_div_const:
  fixes f :: "real \<Rightarrow> real"
  assumes "continuous_on A f"
  shows "continuous_on A (\<lambda>t. f t / c)"
  using continuous_on_mult[OF assms continuous_on_const[of A "inverse c"]] by (simp add: divide_inverse)

lemma cont_Phi:
  fixes x z :: "real \<Rightarrow> real"
  assumes cx: "continuous_on A x" and cz: "continuous_on A z"
    and D: "\<And>t. t \<in> A \<Longrightarrow> 0 \<le> x t \<and> 0 \<le> z t \<and> (x t)^2 + (z t)^2 \<le> 1"
  shows "continuous_on A (\<lambda>t. Phi (x t) (z t))"
proof -
  have e: "(\<lambda>t. Phi (x t) (z t)) = (\<lambda>t. if x t + z t \<le> 1
      then arcsin ((x t - z t) / sqrt (2 - (x t + z t)^2)) / sqrt 2 else arcsin (x t - z t) / sqrt 2)"
    by (simp add: Phi_def)
  have cs: "continuous_on A (\<lambda>t. x t + z t)" by (intro continuous_intros cx cz)
  have cd: "continuous_on A (\<lambda>t. x t - z t)" by (intro continuous_intros cx cz)
  have dsq: "\<And>t. t \<in> A \<Longrightarrow> (x t - z t)^2 \<le> 1"
  proof -
    fix t assume t: "t \<in> A"
    from D[OF t] have "0 \<le> x t * z t" "(x t)^2 + (z t)^2 \<le> 1" by auto
    thus "(x t - z t)^2 \<le> 1" by (simp add: power2_eq_square algebra_simps)
  qed
  show ?thesis unfolding e
  proof (rule continuous_on_cases_le)
    show "continuous_on {t \<in> A. x t + z t \<le> 1} (\<lambda>t. arcsin ((x t - z t) / sqrt (2 - (x t + z t)^2)) / sqrt 2)"
    proof -
      let ?B = "{t \<in> A. x t + z t \<le> 1}"
      have pos: "\<And>t. t \<in> ?B \<Longrightarrow> 0 < 2 - (x t + z t)^2"
      proof -
        fix t assume t: "t \<in> ?B"
        hence "0 \<le> x t + z t" "x t + z t \<le> 1" using D by auto
        hence "(x t + z t)^2 \<le> 1" by (simp add: power_le_one)
        thus "0 < 2 - (x t + z t)^2" by simp
      qed
      have cu: "continuous_on ?B (\<lambda>t. (x t - z t) / sqrt (2 - (x t + z t)^2))"
      proof (rule continuous_on_divide)
        show "continuous_on ?B (\<lambda>t. x t - z t)" by (rule continuous_on_subset[OF cd]) auto
        show "continuous_on ?B (\<lambda>t. sqrt (2 - (x t + z t)^2))"
          by (intro continuous_intros continuous_on_subset[OF cx] continuous_on_subset[OF cz]) auto
        show "\<forall>t\<in>?B. sqrt (2 - (x t + z t)^2) \<noteq> 0" using pos by force
      qed
      have mem: "\<And>t. t \<in> ?B \<Longrightarrow> (x t - z t) / sqrt (2 - (x t + z t)^2) \<in> {-1..1}"
      proof -
        fix t assume t: "t \<in> ?B"
        have hp: "0 < 2 - (x t + z t)^2" by (rule pos[OF t])
        have "(x t + z t)^2 + (x t - z t)^2 = 2 * (x t)^2 + 2 * (z t)^2"
          by (simp add: power2_eq_square algebra_simps)
        moreover have "(x t)^2 + (z t)^2 \<le> 1" using D t by auto
        ultimately have "(x t - z t)^2 \<le> 2 - (x t + z t)^2" by linarith
        hence "((x t - z t) / sqrt (2 - (x t + z t)^2))^2 \<le> 1"
          using hp by (simp add: power_divide real_sqrt_pow2 divide_le_eq_1_pos)
        thus "(x t - z t) / sqrt (2 - (x t + z t)^2) \<in> {-1..1}" by (rule abs_le1)
      qed
      have "continuous_on ?B (\<lambda>t. arcsin ((x t - z t) / sqrt (2 - (x t + z t)^2)))"
        using continuous_on_compose2[OF continuous_on_arcsin' cu] mem by (simp add: image_subset_iff)
      thus ?thesis by (rule cont_div_const)
    qed
    show "continuous_on {t \<in> A. 1 \<le> x t + z t} (\<lambda>t. arcsin (x t - z t) / sqrt 2)"
    proof -
      have "continuous_on A (\<lambda>t. arcsin (x t - z t))"
        using continuous_on_compose2[OF continuous_on_arcsin' cd] dsq abs_le1 by (simp add: image_subset_iff)
      hence "continuous_on A (\<lambda>t. arcsin (x t - z t) / sqrt 2)" by (rule cont_div_const)
      thus ?thesis by (rule continuous_on_subset) auto
    qed
    show "continuous_on A (\<lambda>t. x t + z t)" by (rule cs)
    show "\<And>t. t \<in> A \<Longrightarrow> x t + z t = 1 \<Longrightarrow>
        arcsin ((x t - z t) / sqrt (2 - (x t + z t)^2)) / sqrt 2 = arcsin (x t - z t) / sqrt 2" by simp
  qed
qed

lemma countable_isolated:
  fixes A :: "real set"
  assumes "\<And>a. a \<in> A \<Longrightarrow> \<exists>e>0. \<forall>b\<in>A. \<bar>b - a\<bar> < e \<longrightarrow> b = a"
  shows "countable A"
proof -
  have "\<forall>a\<in>A. \<exists>e. 0 < e \<and> (\<forall>b\<in>A. \<bar>b - a\<bar> < e \<longrightarrow> b = a)" using assms by blast
  from bchoice[OF this] obtain e where e: "\<And>a. a \<in> A \<Longrightarrow> 0 < e a \<and> (\<forall>b\<in>A. \<bar>b - a\<bar> < e a \<longrightarrow> b = a)" by blast
  have "\<forall>a\<in>A. \<exists>q. q \<in> Rats \<and> a < q \<and> q < a + e a / 2"
    using e Rats_dense_in_real[of _ "_ + _ / 2"] by (metis add_strict_increasing half_gt_zero_iff less_add_same_cancel1 order_less_le)
  from bchoice[OF this] obtain q where q: "\<And>a. a \<in> A \<Longrightarrow> q a \<in> Rats \<and> a < q a \<and> q a < a + e a / 2" by blast
  have inj: "inj_on q A"
  proof (rule inj_onI)
    fix a b assume ab: "a \<in> A" "b \<in> A" "q a = q b"
    show "a = b"
    proof (cases "e b \<le> e a")
      case True
      have "\<bar>b - a\<bar> < e a" using q[OF ab(1)] q[OF ab(2)] e[OF ab(1)] e[OF ab(2)] ab(3) True by (simp add: abs_less_iff)
      thus ?thesis using e[OF ab(1)] ab(2) by blast
    next
      case False
      have "\<bar>a - b\<bar> < e b" using q[OF ab(1)] q[OF ab(2)] e[OF ab(1)] e[OF ab(2)] ab(3) False by (simp add: abs_less_iff)
      thus ?thesis using e[OF ab(2)] ab(1) by blast
    qed
  qed
  have "countable (q ` A)" by (rule countable_subset[OF _ countable_rat]) (use q in auto)
  thus ?thesis using inj by (rule countable_image_inj_on)
qed

lemma Phi10: "Phi 1 0 = (pi / 2) / sqrt 2"
  unfolding Phi_def by (simp add: arcsin_1)

lemma Phi01: "Phi 0 1 = - ((pi / 2) / sqrt 2)"
proof -
  have a: "(0::real) + 1 \<le> 1" by simp
  have b: "((0::real) - 1) / sqrt (2 - (0 + 1)^2) = -1" by simp
  have "Phi 0 1 = arcsin (-1) / sqrt 2" unfolding Phi_def if_P[OF a] b ..
  also have "... = (- (pi / 2)) / sqrt 2" by (simp only: arcsin_minus_1)
  also have "... = - ((pi / 2) / sqrt 2)" by (rule minus_divide_left[symmetric])
  finally show ?thesis .
qed

lemma half_gen: "(a::real) / b = 2 * ((a / 2) / b)"
  by (cases "b = 0") (simp_all add: field_simps)

lemma pis_eq: "pi / sqrt 2 = 2 * ((pi / 2) / sqrt 2)"
  by (rule half_gen)

lemma final_ineq:
  fixes G t0 t1 w :: real
  assumes "0 \<le> (G * t1 + (- w)) - (G * t0 + w)"
  shows "2 * w \<le> G * (t1 - t0)"
  using assms by (simp add: algebra_simps)

section \<open>The theorem\<close>

text \<open>Minimal transfer time of the qubit--bus--qubit relay. Hypotheses: x and z are continuous on [0, T], non-negative, with x\<^latex>\<open>\textsuperscript{2}\<close> + z\<^latex>\<open>\textsuperscript{2}\<close> <= 1; x 0 = 1 and z T = 1 (the excitation starts in A and ends in B); they are differentiable outside a countable set S, with both derivatives bounded by G times the square root of the bus occupation. Conclusion: pi / sqrt 2 <= G T.\<close>

theorem relay_minimal_time:
  fixes x z x' z' :: "real \<Rightarrow> real" and G T :: real and S :: "real set"
  assumes T: "0 \<le> T" and S: "countable S"
    and cx: "continuous_on {0..T} x" and cz: "continuous_on {0..T} z"
    and D: "\<forall>t\<in>{0..T}. 0 \<le> x t \<and> 0 \<le> z t \<and> (x t)^2 + (z t)^2 \<le> 1"
    and x0: "x 0 = 1" and zT: "z T = 1"
    and der: "\<forall>t\<in>{0<..<T} - S. (x has_real_derivative x' t) (at t) \<and> (z has_real_derivative z' t) (at t)"
    and bnd: "\<forall>t\<in>{0<..<T} - S. \<bar>x' t\<bar> \<le> G * sqrt (1 - (x t)^2 - (z t)^2) \<and> \<bar>z' t\<bar> \<le> G * sqrt (1 - (x t)^2 - (z t)^2)"
  shows "pi / sqrt 2 \<le> G * T"
proof -
  have Dt: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> x t \<and> 0 \<le> z t \<and> (x t)^2 + (z t)^2 \<le> 1" using D by blast
  have z0: "z 0 = 0"
  proof -
    have "(z 0)^2 \<le> 0" using Dt[of 0] T x0 by simp
    thus ?thesis by simp
  qed
  have xT: "x T = 0"
  proof -
    have "(x T)^2 \<le> 0" using Dt[of T] T zT by simp
    thus ?thesis by simp
  qed
  have Tpos: "0 < T"
  proof (rule ccontr)
    assume "\<not> 0 < T"
    with T have "T = 0" by simp
    thus False using zT z0 by simp
  qed
  \<comment> \<open>G > 0\<close>
  have Gpos: "0 < G"
  proof (rule ccontr)
    assume "\<not> 0 < G"
    hence G0: "G \<le> 0" by simp
    have xd: "\<And>u. u \<in> {0..T} - (S \<union> {0, T}) \<Longrightarrow> (x has_derivative (\<lambda>h. 0)) (at u within {0..T})"
    proof -
      fix u assume u: "u \<in> {0..T} - (S \<union> {0, T})"
      hence ui: "u \<in> {0<..<T} - S" by auto
      have "x' u = 0"
      proof -
        have uD: "u \<in> {0..T}" using ui by auto
        have hD: "0 \<le> 1 - (x u)^2 - (z u)^2" using Dt[OF uD] by linarith
        have "G * sqrt (1 - (x u)^2 - (z u)^2) \<le> 0" by (rule mult_nonpos_nonneg[OF G0 real_sqrt_ge_zero[OF hD]])
        moreover have "\<bar>x' u\<bar> \<le> G * sqrt (1 - (x u)^2 - (z u)^2)" using bnd ui by blast
        ultimately have "\<bar>x' u\<bar> \<le> 0" by (rule order_trans[rotated])
        thus ?thesis by simp
      qed
      moreover have "(x has_real_derivative x' u) (at u)" using der ui by blast
      ultimately have "(x has_field_derivative 0) (at u)" by simp
      hence "(x has_derivative (\<lambda>h. 0)) (at u)"
      proof -
        assume hf: "(x has_field_derivative 0) (at u)"
        have e: "((*) (0::real)) = (\<lambda>h. 0)" by (rule ext) simp
        show ?thesis using hf unfolding has_field_derivative_def e .
      qed
      thus "(x has_derivative (\<lambda>h. 0)) (at u within {0..T})" by (rule has_derivative_at_withinI)
    qed
    have "x T = 1"
      by (rule has_derivative_zero_unique_strong_interval[of "S \<union> {0, T}" 0 T x 1 T])
         (use S cx x0 xd T in \<open>auto\<close>)
    thus False using xT by simp
  qed
  have G0: "0 \<le> G" using Gpos by simp
  \<comment> \<open>the times t1 and t0\<close>
  define Z where "Z = {t \<in> {0..T}. z t = 1}"
  have Zc: "closed Z"
  proof -
    have "Z = z -` {1} \<inter> {0..T}" unfolding Z_def by auto
    moreover have "closed (z -` {1} \<inter> {0..T})"
      using continuous_on_closed_vimage[of "{0..T}" z] cz by auto
    ultimately show ?thesis by simp
  qed
  have ZT: "T \<in> Z" unfolding Z_def using zT T by auto
  have Zb: "bdd_below Z" unfolding Z_def by (intro bdd_belowI[of _ 0]) auto
  define t1 where "t1 = Inf Z"
  have t1Z: "t1 \<in> Z" unfolding t1_def by (rule closed_contains_Inf[OF _ Zb Zc]) (use ZT in auto)
  have t1min: "\<And>t. t \<in> {0..T} \<Longrightarrow> z t = 1 \<Longrightarrow> t1 \<le> t"
    unfolding t1_def by (rule cInf_lower[OF _ Zb]) (simp add: Z_def)
  have t1r: "0 \<le> t1" "t1 \<le> T" "z t1 = 1" using t1Z unfolding Z_def by auto
  have xt1: "x t1 = 0"
  proof -
    have "(x t1)^2 \<le> 0" using Dt[of t1] t1r by simp
    thus ?thesis by simp
  qed
  define X where "X = {t \<in> {0..t1}. x t = 1}"
  have Xc: "closed X"
  proof -
    have "continuous_on {0..t1} x" by (rule continuous_on_subset[OF cx]) (use t1r in auto)
    hence "closed (x -` {1} \<inter> {0..t1})" using continuous_on_closed_vimage[of "{0..t1}" x] by auto
    moreover have "X = x -` {1} \<inter> {0..t1}" unfolding X_def by auto
    ultimately show ?thesis by simp
  qed
  have X0: "0 \<in> X" unfolding X_def using x0 t1r by auto
  have Xb: "bdd_above X" unfolding X_def by (intro bdd_aboveI[of _ t1]) auto
  define t0 where "t0 = Sup X"
  have t0X: "t0 \<in> X" unfolding t0_def by (rule closed_contains_Sup[OF _ Xb Xc]) (use X0 in auto)
  have t0max: "\<And>t. t \<in> {0..t1} \<Longrightarrow> x t = 1 \<Longrightarrow> t \<le> t0"
    unfolding t0_def by (rule cSup_upper[OF _ Xb]) (simp add: X_def)
  have t0r: "0 \<le> t0" "t0 \<le> t1" "x t0 = 1" using t0X unfolding X_def by auto
  have t01: "t0 < t1"
  proof -
    have "t0 \<noteq> t1" using t0r(3) xt1 by auto
    thus ?thesis using t0r(2) by simp
  qed
  have zt0: "z t0 = 0"
  proof -
    have "(z t0)^2 \<le> 0" using Dt[of t0] t0r t1r by simp
    thus ?thesis by simp
  qed
  have inner_x: "\<And>u. t0 < u \<Longrightarrow> u < t1 \<Longrightarrow> x u \<noteq> 1"
  proof
    fix u assume "t0 < u" "u < t1" "x u = 1"
    hence "u \<le> t0" using t0max[of u] t0r by simp
    thus False using \<open>t0 < u\<close> by simp
  qed
  have inner_z: "\<And>u. t0 < u \<Longrightarrow> u < t1 \<Longrightarrow> z u \<noteq> 1"
  proof
    fix u assume "t0 < u" "u < t1" "z u = 1"
    hence "t1 \<le> u" using t1min[of u] t0r t1r by simp
    thus False using \<open>u < t1\<close> by simp
  qed
  \<comment> \<open>the function h\<close>
  define h where "h = (\<lambda>u. G * u + Phi (x u) (z u))"
  have hcont: "continuous_on {t0..t1} h"
  proof -
    have sub: "{t0..t1} \<subseteq> {0..T}" using t0r t1r by auto
    have "continuous_on {t0..t1} (\<lambda>t. Phi (x t) (z t))"
      by (rule cont_Phi) (use sub continuous_on_subset[OF cx sub] continuous_on_subset[OF cz sub] Dt in auto)
    thus ?thesis unfolding h_def by (intro continuous_intros)
  qed
  \<comment> \<open>the countable set of exceptions\<close>
  define B where "B = {t. \<exists>c. c \<noteq> 0 \<and> ((\<lambda>u. x u + z u) has_real_derivative c) (at t) \<and> x t + z t = 1}"
  have Bc: "countable B"
  proof (rule countable_isolated)
    fix a assume "a \<in> B"
    then obtain c where c: "c \<noteq> 0" "((\<lambda>u. x u + z u) has_real_derivative c) (at a)" "x a + z a = 1" unfolding B_def by blast
    have q: "((\<lambda>y. ((x y + z y) - (x a + z a)) / (y - a)) \<longlongrightarrow> c) (at a)"
      using c(2) by (simp add: has_field_derivative_iff)
    have "eventually (\<lambda>y. ((x y + z y) - (x a + z a)) / (y - a) \<noteq> 0) (at a)"
      by (rule tendsto_imp_eventually_ne[OF q c(1)])
    then obtain d where d: "0 < d" "\<And>y. y \<noteq> a \<Longrightarrow> dist y a < d \<Longrightarrow> ((x y + z y) - (x a + z a)) / (y - a) \<noteq> 0"
      unfolding eventually_at by blast
    show "\<exists>e>0. \<forall>b\<in>B. \<bar>b - a\<bar> < e \<longrightarrow> b = a"
    proof (intro exI[of _ d] conjI allI ballI impI)
      show "0 < d" by (rule d(1))
      fix b assume b: "b \<in> B" "\<bar>b - a\<bar> < d"
      show "b = a"
      proof (rule ccontr)
        assume ne: "b \<noteq> a"
        have "((x b + z b) - (x a + z a)) / (b - a) \<noteq> 0" using d(2)[OF ne] b(2) by (simp add: dist_real_def)
        hence "x b + z b \<noteq> x a + z a" by simp
        moreover have "x b + z b = 1" using b(1) unfolding B_def by blast
        ultimately show False using c(3) by simp
      qed
    qed
  qed
  define E where "E = S \<union> B"
  have Ec: "countable E" unfolding E_def using S Bc by blast
  define f' where "f' = (\<lambda>u. if u \<in> {t0<..<t1} - E then deriv h u else 0)"
  have good: "\<And>u. u \<in> {t0<..<t1} - E \<Longrightarrow> \<exists>c. 0 \<le> c \<and> (h has_real_derivative c) (at u)"
  proof -
    fix u assume u: "u \<in> {t0<..<t1} - E"
    hence u1: "t0 < u" "u < t1" and uS: "u \<notin> S" and uB: "u \<notin> B" unfolding E_def by auto
    have uT: "u \<in> {0<..<T}" using u1 t0r t1r by auto
    have ui: "u \<in> {0<..<T} - S" using uT uS by blast
    have uD: "u \<in> {0..T}" using uT by auto
    from der ui have hx: "(x has_real_derivative x' u) (at u)" and hz: "(z has_real_derivative z' u) (at u)" by blast+
    have hs: "x u + z u = 1 \<Longrightarrow> x' u + z' u = 0"
    proof (rule ccontr)
      assume "x u + z u = 1" "x' u + z' u \<noteq> 0"
      moreover have "((\<lambda>v. x v + z v) has_real_derivative x' u + z' u) (at u)" by (rule DERIV_add[OF hx hz])
      ultimately have "u \<in> B" unfolding B_def by blast
      thus False using uB by simp
    qed
    show "\<exists>c. 0 \<le> c \<and> (h has_real_derivative c) (at u)"
      unfolding h_def
      by (rule key_deriv[OF G0 hx hz _ _ _ inner_x[OF u1] inner_z[OF u1] _ _ hs])
         (use Dt[OF uD] bnd ui in auto)
  qed
  have fder: "\<And>u. u \<in> {t0<..<t1} - E \<Longrightarrow> (h has_vector_derivative f' u) (at u)"
  proof -
    fix u assume u: "u \<in> {t0<..<t1} - E"
    from good[OF u] obtain c where c: "0 \<le> c" "(h has_real_derivative c) (at u)" by blast
    have "f' u = c" unfolding f'_def using DERIV_imp_deriv[OF c(2)] by (simp only: if_P[OF u])
    thus "(h has_vector_derivative f' u) (at u)" using c(2) by (simp add: has_real_derivative_iff_has_vector_derivative)
  qed
  have fnn: "\<And>u. 0 \<le> f' u"
  proof -
    fix u
    show "0 \<le> f' u"
    proof (cases "u \<in> {t0<..<t1} - E")
      case True
      from good[OF True] obtain c where c: "0 \<le> c" "(h has_real_derivative c) (at u)" by blast
      have "f' u = c" unfolding f'_def using DERIV_imp_deriv[OF c(2)] by (simp only: if_P[OF True])
      thus ?thesis using c(1) by simp
    next
      case False
      hence "f' u = 0" unfolding f'_def by (rule if_not_P)
      thus ?thesis by simp
    qed
  qed
  have ftc: "(f' has_integral (h t1 - h t0)) {t0..t1}"
    by (rule fundamental_theorem_of_calculus_interior_strong[OF Ec less_imp_le[OF t01] fder hcont])
  have hnn: "0 \<le> h t1 - h t0" by (rule has_integral_nonneg[OF ftc]) (simp add: fnn)
  \<comment> \<open>values at the endpoints\<close>
  have P0: "Phi (x t0) (z t0) = (pi / 2) / sqrt 2" unfolding t0r(3) zt0 by (rule Phi10)
  have P1: "Phi (x t1) (z t1) = - ((pi / 2) / sqrt 2)" unfolding xt1 t1r(3) by (rule Phi01)
  have "pi / sqrt 2 \<le> G * (t1 - t0)"
  proof -
    have "0 \<le> (G * t1 + (- ((pi / 2) / sqrt 2))) - (G * t0 + (pi / 2) / sqrt 2)"
      using hnn unfolding h_def P0 P1 .
    hence "2 * ((pi / 2) / sqrt 2) \<le> G * (t1 - t0)" by (rule final_ineq)
    thus ?thesis unfolding pis_eq[symmetric] .
  qed
  also have "G * (t1 - t0) \<le> G * T"
    by (rule mult_left_mono[OF _ G0]) (use t0r(1) t1r(2) in linarith)
  finally show ?thesis .
qed


end
