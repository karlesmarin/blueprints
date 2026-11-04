(*  Title:      Relay_Asymptotic.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The final chain of the asymptotic floor: from the frontier bound on the integrated occupation to
    the floor 2 sqrt(2 gamma delta)/G (1 - o(1)), and the arithmetic of the protocol that attains it.
*)
theory Relay_Asymptotic
  imports "HOL-Analysis.Analysis"
begin

section \<open>The chain of the asymptotic floor\<close>

text \<open>Arithmetic and geometric means: gamma T + c delta/(G\<^latex>\<open>\textsuperscript{2}\<close> T) is at least
2 sqrt(c gamma delta)/G at every duration T.\<close>

lemma time_amgm:
  fixes \<gamma> \<delta> G T c :: real
  assumes g: "0 \<le> \<gamma>" and d: "0 \<le> \<delta>" and c: "0 \<le> c" and G: "0 < G" and T: "0 < T"
  shows "2 * sqrt (c * \<gamma> * \<delta>) / G \<le> \<gamma> * T + c * \<delta> / (G\<^sup>2 * T)"
proof -
  define p where "p = sqrt (\<gamma> * T)"
  define q where "q = sqrt (c * \<delta> / (G\<^sup>2 * T))"
  have p2: "p\<^sup>2 = \<gamma> * T" unfolding p_def using g T by simp
  have q2: "q\<^sup>2 = c * \<delta> / (G\<^sup>2 * T)" unfolding q_def using c d G T by simp
  have pq: "p * q = sqrt (c * \<gamma> * \<delta>) / G"
  proof -
    have "p * q = sqrt (\<gamma> * T * (c * \<delta> / (G\<^sup>2 * T)))" unfolding p_def q_def by (rule real_sqrt_mult[symmetric])
    also have "\<gamma> * T * (c * \<delta> / (G\<^sup>2 * T)) = (c * \<gamma> * \<delta>) / G\<^sup>2" using T by (simp add: field_simps)
    also have "sqrt \<dots> = sqrt (c * \<gamma> * \<delta>) / G" using G by (simp add: real_sqrt_divide)
    finally show ?thesis .
  qed
  have "0 \<le> (p - q)\<^sup>2" by simp
  hence "2 * (p * q) \<le> p\<^sup>2 + q\<^sup>2" by (simp add: power2_eq_square algebra_simps)
  thus ?thesis using p2 q2 pq by simp
qed

text \<open>The elementary bound 1 - exp(-s) >= s (1 - s/2) for s >= 0.\<close>

lemma one_minus_exp_ge:
  fixes s :: real
  assumes s: "0 \<le> s"
  shows "s * (1 - s / 2) \<le> 1 - exp (- s)"
proof -
  define f where "f = (\<lambda>u::real. 1 - exp (- u) - u + u\<^sup>2 / 2)"
  define f' where "f' = (\<lambda>u::real. exp (- u) - 1 + u)"
  have df: "\<And>u. (f has_real_derivative f' u) (at u)"
    unfolding f_def f'_def by (auto intro!: derivative_eq_intros simp: power2_eq_square)
  have f'nn: "\<And>u. 0 \<le> f' u"
  proof -
    fix u :: real
    have "1 + (- u) \<le> exp (- u)" by (rule exp_ge_add_one_self)
    thus "0 \<le> f' u" unfolding f'_def by simp
  qed
  have "f 0 \<le> f s"
  proof (rule DERIV_nonneg_imp_increasing_open[OF s])
    show "\<And>u. 0 < u \<Longrightarrow> u < s \<Longrightarrow> \<exists>y. (f has_real_derivative y) (at u) \<and> 0 \<le> y"
      using df f'nn by blast
    show "continuous_on {0..s} f" unfolding f_def by (intro continuous_intros) simp_all
  qed
  moreover have "f 0 = 0" unfolding f_def by simp
  ultimately have "0 \<le> 1 - exp (- s) - s + s\<^sup>2 / 2" unfolding f_def by simp
  thus ?thesis by (simp add: power2_eq_square algebra_simps)
qed

text \<open>The quantitative form of the asymptotic floor. Its hypotheses are what the proof of the theorem
obtains at a fixed control and duration T: the rescaled survival satisfies P <= exp(-s) with
s = gamma T + delta I, and the frontier bound gives I >= (2 - eta)/(G\<^latex>\<open>\textsuperscript{2}\<close> T). Then the loss
1 - P is at least s0 (1 - s0/2) with s0 = 2 sqrt((2 - eta) gamma delta)/G, whatever T is; as eta and
s0 tend to 0 this is 2 sqrt(2 gamma delta)/G (1 - o(1)).\<close>

theorem asymptotic_floor_chain:
  fixes \<gamma> \<delta> G T I P \<eta> s0 :: real
  assumes g: "0 \<le> \<gamma>" and d: "0 \<le> \<delta>" and G: "0 < G" and T: "0 < T"
    and \<eta>: "\<eta> \<le> 2"
    and fr: "(2 - \<eta>) / (G\<^sup>2 * T) \<le> I"
    and P: "P \<le> exp (- (\<gamma> * T + \<delta> * I))"
    and that: "s0 = 2 * sqrt ((2 - \<eta>) * \<gamma> * \<delta>) / G"
  shows "s0 * (1 - s0 / 2) \<le> 1 - P"
proof -
  have c: "0 \<le> 2 - \<eta>" using \<eta> by simp
  have s0: "s0 \<le> \<gamma> * T + (2 - \<eta>) * \<delta> / (G\<^sup>2 * T)"
    unfolding that by (rule time_amgm[OF g d c G T])
  have "(2 - \<eta>) * \<delta> / (G\<^sup>2 * T) = \<delta> * ((2 - \<eta>) / (G\<^sup>2 * T))" by simp
  also have "\<dots> \<le> \<delta> * I" by (rule mult_left_mono[OF fr d])
  finally have ss: "s0 \<le> \<gamma> * T + \<delta> * I" using s0 by linarith
  have s0nn: "0 \<le> s0" unfolding that using G g d c by simp
  have "exp (- (\<gamma> * T + \<delta> * I)) \<le> exp (- s0)" using ss by simp
  hence "1 - exp (- s0) \<le> 1 - P" using P by linarith
  moreover have "s0 * (1 - s0 / 2) \<le> 1 - exp (- s0)" by (rule one_minus_exp_ge[OF s0nn])
  ultimately show ?thesis by linarith
qed

section \<open>The arithmetic of the attaining protocol\<close>

text \<open>The numerical steps in the proof that the constant is attained: with alpha, beta <= 0.01 the
protocol ends before t* = 0.02/gamma, and the coefficient 4.2/(2 sqrt 2) of beta is below 1.5.\<close>

lemma attain_time_margin:
  fixes \<alpha> \<beta> :: real
  assumes a0: "0 \<le> \<alpha>" and a: "\<alpha> \<le> 0.01" and b0: "0 \<le> \<beta>" and b: "\<beta> \<le> 0.01"
  shows "sqrt 2 * \<alpha> / (1 - \<alpha>) + 2.1 * \<alpha> * \<beta> \<le> 0.0145"
proof -
  have s2: "sqrt 2 \<le> 1.4143"
  proof (rule real_le_lsqrt)
    show "(2::real) \<le> 1.4143\<^sup>2" by (simp add: power2_eq_square)
  qed simp_all
  have den: "0.99 \<le> 1 - \<alpha>" using a by simp
  have "sqrt 2 * \<alpha> / (1 - \<alpha>) \<le> 1.4143 * 0.01 / 0.99"
  proof (rule frac_le)
    show "0 \<le> 1.4143 * (0.01::real)" by simp
    show "sqrt 2 * \<alpha> \<le> 1.4143 * 0.01" by (rule mult_mono[OF s2 a]) (use a0 in simp_all)
    show "(0::real) < 0.99" by simp
    show "0.99 \<le> 1 - \<alpha>" by (rule den)
  qed
  moreover have "2.1 * \<alpha> * \<beta> \<le> 2.1 * 0.01 * 0.01"
    by (intro mult_mono) (use a0 a b0 b in simp_all)
  ultimately show ?thesis by simp
qed

lemma attain_coefficient: "4.2 / (2 * sqrt 2) < (1.5::real)"
proof -
  have "(1.4::real) < sqrt 2"
  proof (rule real_less_rsqrt)
    show "(1.4::real)\<^sup>2 < 2" by (simp add: power2_eq_square)
  qed
  hence "4.2 < 1.5 * (2 * sqrt 2)" by simp
  thus ?thesis by (simp add: divide_less_eq)
qed

end
