(*  Title:      Relay_Extensions.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Weighted forms of the loss floor: ramped couplings, a closed-form estimate valid at every duration,
    the receiver's bus term with an excess rate, and the norm balance with an excess rate per element.
*)
theory Relay_Extensions
  imports Relay_Loss_Floor
begin

text \<open>Notation as in the theory of the loss floor: n is the squared norm of the rescaled state, x, y, z
the moduli of the rescaled amplitudes of the emitter, the bus and the receiver. This theory replaces the
constant coupling bound G by a time-dependent envelope m(t) (Cauchy--Schwarz with a weight), computes the
envelope integral of ramped couplings, gives a closed-form consequence of the floor valid at every
duration, and proves the bus term and the norm balance of the floor with an excess rate per element.\<close>

section \<open>Auxiliary lemmas\<close>

lemma quad_disc:
  fixes A B C :: real
  assumes q: "\<And>l. 0 \<le> A * l\<^sup>2 - 2 * B * l + C" and A: "0 \<le> A"
  shows "B\<^sup>2 \<le> A * C"
proof (cases "A = 0")
  case True
  show ?thesis
  proof (cases "B = 0")
    case True
    thus ?thesis using \<open>A = 0\<close> by simp
  next
    case False
    have "0 \<le> A * ((C + 1) / (2 * B))\<^sup>2 - 2 * B * ((C + 1) / (2 * B)) + C" by (rule q)
    also have "\<dots> = -1" using \<open>A = 0\<close> False by (simp add: field_simps)
    finally show ?thesis by simp
  qed
next
  case False
  hence A0: "0 < A" using A by simp
  have "0 \<le> A * (B / A)\<^sup>2 - 2 * B * (B / A) + C" by (rule q)
  also have "\<dots> = C - B\<^sup>2 / A" using A0 by (simp add: field_simps power2_eq_square)
  finally have "B\<^sup>2 / A \<le> C" by simp
  thus ?thesis using A0 by (simp add: divide_le_eq mult.commute)
qed

text \<open>Cauchy--Schwarz for continuous functions with a weight.\<close>

lemma cauchy_schwarz_weighted:
  fixes m y :: "real \<Rightarrow> real" and a b :: real
  assumes ab: "a \<le> b" and mc: "continuous_on {a..b} m" and yc: "continuous_on {a..b} y"
  shows "(integral {a..b} (\<lambda>t. m t * y t))\<^sup>2
           \<le> integral {a..b} (\<lambda>t. (m t)\<^sup>2) * integral {a..b} (\<lambda>t. (y t)\<^sup>2)"
proof -
  define A where "A = integral {a..b} (\<lambda>t. (m t)\<^sup>2)"
  define B where "B = integral {a..b} (\<lambda>t. m t * y t)"
  define C where "C = integral {a..b} (\<lambda>t. (y t)\<^sup>2)"
  have m2c: "continuous_on {a..b} (\<lambda>t. (m t)\<^sup>2)" using mc by (intro continuous_intros)
  have myc: "continuous_on {a..b} (\<lambda>t. m t * y t)" using mc yc by (intro continuous_intros)
  have y2c: "continuous_on {a..b} (\<lambda>t. (y t)\<^sup>2)" using yc by (intro continuous_intros)
  have Ai: "((\<lambda>t. (m t)\<^sup>2) has_integral A) {a..b}" unfolding A_def
    using integrable_continuous_real[OF m2c] by (rule integrable_integral)
  have Bi: "((\<lambda>t. m t * y t) has_integral B) {a..b}" unfolding B_def
    using integrable_continuous_real[OF myc] by (rule integrable_integral)
  have Ci: "((\<lambda>t. (y t)\<^sup>2) has_integral C) {a..b}" unfolding C_def
    using integrable_continuous_real[OF y2c] by (rule integrable_integral)
  have q: "0 \<le> A * l\<^sup>2 - 2 * B * l + C" for l
  proof -
    have tot: "((\<lambda>t. l\<^sup>2 * (m t)\<^sup>2 - (2 * l) * (m t * y t) + (y t)\<^sup>2)
                 has_integral l\<^sup>2 * A - (2 * l) * B + C) {a..b}"
      by (rule has_integral_add[OF has_integral_diff[OF has_integral_mult_right[OF Ai]
            has_integral_mult_right[OF Bi]] Ci])
    have "0 \<le> l\<^sup>2 * A - (2 * l) * B + C"
    proof (rule has_integral_nonneg[OF tot])
      fix t assume "t \<in> {a..b}"
      have "l\<^sup>2 * (m t)\<^sup>2 - (2 * l) * (m t * y t) + (y t)\<^sup>2 = (l * m t - y t)\<^sup>2"
        by (simp add: power2_eq_square algebra_simps)
      thus "0 \<le> l\<^sup>2 * (m t)\<^sup>2 - (2 * l) * (m t * y t) + (y t)\<^sup>2" by simp
    qed
    thus ?thesis by (simp add: algebra_simps)
  qed
  have A0: "0 \<le> A" by (rule has_integral_nonneg[OF Ai]) simp
  show ?thesis using quad_disc[OF q A0] unfolding A_def B_def C_def .
qed

text \<open>One-sided fundamental theorem of calculus with a continuous majorant, countably many exceptions.\<close>

lemma ftc_le:
  fixes n n' h :: "real \<Rightarrow> real" and a b :: real and S :: "real set"
  assumes S: "countable S" and ab: "a \<le> b"
    and nc: "continuous_on {a..b} n" and hc: "continuous_on {a..b} h"
    and der: "\<And>t. t \<in> {a<..<b} - S \<Longrightarrow> (n has_real_derivative n' t) (at t) \<and> n' t \<le> h t"
  shows "n b - n a \<le> integral {a..b} h"
proof -
  define f where "f = (\<lambda>t. if t \<in> {a<..<b} - S then n' t else h t)"
  have fd: "\<And>t. t \<in> {a<..<b} - S \<Longrightarrow> (n has_vector_derivative f t) (at t)"
  proof -
    fix t assume t: "t \<in> {a<..<b} - S"
    have "f t = n' t" unfolding f_def using t by simp
    thus "(n has_vector_derivative f t) (at t)" using der[OF t]
      by (simp add: has_real_derivative_iff_has_vector_derivative)
  qed
  have ftc: "(f has_integral n b - n a) {a..b}"
    by (rule fundamental_theorem_of_calculus_interior_strong[OF S ab fd nc])
  have hi: "(h has_integral integral {a..b} h) {a..b}"
    using integrable_continuous_real[OF hc] by (rule integrable_integral)
  have fle: "\<And>t. t \<in> {a..b} \<Longrightarrow> f t \<le> h t"
    unfolding f_def using der by auto
  show ?thesis by (rule has_integral_le[OF ftc hi fle])
qed

section \<open>The floor with a coupling envelope\<close>

text \<open>If the receiver's coupling is bounded by an envelope m(t), so that |z'| <= m(t) y, the floor holds
with G\<^latex>\<open>\textsuperscript{2}\<close> T replaced by the envelope integral J = int m\<^latex>\<open>\textsuperscript{2}\<close>.\<close>

theorem weighted_loss_floor:
  fixes n y z m n' z' :: "real \<Rightarrow> real" and T \<delta> :: real and S :: "real set"
  assumes T: "0 < T" and d0: "0 \<le> \<delta>" and S: "countable S"
    and nc: "continuous_on {0..T} n" and yc: "continuous_on {0..T} y" and zc: "continuous_on {0..T} z"
    and mc: "continuous_on {0..T} m" and m0: "\<forall>t\<in>{0..T}. 0 \<le> m t"
    and y0: "\<forall>t\<in>{0..T}. 0 \<le> y t"
    and J: "0 < integral {0..T} (\<lambda>t. (m t)\<^sup>2)"
    and n0: "n 0 \<le> 1" and z0: "z 0 = 0" and zT: "(z T)\<^sup>2 \<le> n T"
    and der: "\<forall>t\<in>{0<..<T} - S. (n has_real_derivative n' t) (at t) \<and> (z has_real_derivative z' t) (at t)"
    and bnd: "\<forall>t\<in>{0<..<T} - S. n' t \<le> - \<delta> * (y t)\<^sup>2 \<and> \<bar>z' t\<bar> \<le> m t * y t"
  shows "(z T)\<^sup>2 * (1 + \<delta> / integral {0..T} (\<lambda>t. (m t)\<^sup>2)) \<le> 1"
proof -
  define I where "I = integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
  define K where "K = integral {0..T} (\<lambda>t. (m t)\<^sup>2)"
  define A where "A = (z T)\<^sup>2"
  have s1: "n T - n 0 \<le> - \<delta> * I" unfolding I_def
    by (rule ftc_decrease[OF S T nc yc]) (use der bnd in blast)
  have s1': "\<delta> * I \<le> 1 - A" using s1 n0 zT unfolding A_def by linarith
  have myc: "continuous_on {0..T} (\<lambda>t. m t * y t)" using mc yc by (intro continuous_intros)
  have b2: "\<bar>z T - z 0\<bar> \<le> integral {0..T} (\<lambda>t. m t * y t)"
    by (rule ftc_bound[where F' = z', OF S less_imp_le[OF T] zc myc]) (use m0 y0 der bnd in auto)
  hence "\<bar>z T\<bar> \<le> integral {0..T} (\<lambda>t. m t * y t)" using z0 by simp
  hence "(z T)\<^sup>2 \<le> (integral {0..T} (\<lambda>t. m t * y t))\<^sup>2"
    using power_mono[of "\<bar>z T\<bar>" _ 2] abs_ge_zero by simp
  also have "\<dots> \<le> K * I" unfolding K_def I_def
    by (rule cauchy_schwarz_weighted[OF less_imp_le[OF T] mc yc])
  finally have s2: "A \<le> K * I" unfolding A_def .
  have K0: "0 < K" using J unfolding K_def .
  have "A / K \<le> I" using s2 K0 by (simp add: divide_le_eq mult.commute)
  hence "\<delta> * (A / K) \<le> \<delta> * I" using d0 by (rule mult_left_mono)
  hence "A * (\<delta> / K) \<le> \<delta> * I" by (simp add: algebra_simps)
  hence "A * (1 + \<delta> / K) \<le> 1" using s1' by (simp add: algebra_simps)
  thus ?thesis unfolding A_def K_def .
qed

section \<open>Ramped couplings\<close>

definition ramp_env :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "ramp_env S G T t = min (min (S * t) (S * (T - t))) G"

text \<open>A coupling that starts and ends at zero, changes at most at slope S (in norm) and is bounded by G
stays under the trapezoidal envelope min(S t, S (T - t), G). The slope bound is stated as a Lipschitz
condition, which for absolutely continuous couplings is the bound on the norm of the derivative.\<close>

lemma ramp_envelope:
  fixes g :: "real \<Rightarrow> 'a::real_normed_vector" and S G T :: real
  assumes lip: "\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}. norm (g s - g t) \<le> S * \<bar>s - t\<bar>"
    and g0: "g 0 = 0" and gT: "g T = 0" and gG: "\<forall>t\<in>{0..T}. norm (g t) \<le> G"
    and t: "t \<in> {0..T}"
  shows "norm (g t) \<le> ramp_env S G T t"
proof -
  have T0: "0 \<in> {0..T}" and TT: "T \<in> {0..T}" using t by auto
  have "norm (g t) = norm (g t - g 0)" using g0 by simp
  also have "\<dots> \<le> S * \<bar>t - 0\<bar>" using lip t T0 by blast
  finally have l: "norm (g t) \<le> S * t" using t by simp
  have "norm (g t) = norm (g t - g T)" using gT by simp
  also have "\<dots> \<le> S * \<bar>t - T\<bar>" using lip t TT by blast
  also have "\<bar>t - T\<bar> = T - t" using t by simp
  finally have r: "norm (g t) \<le> S * (T - t)" .
  show ?thesis unfolding ramp_env_def using l r gG t by simp
qed

lemma ramp_env_cont: "continuous_on A (ramp_env S G T)"
  unfolding ramp_env_def by (intro continuous_intros)

lemma ramp_env_nonneg:
  assumes "0 \<le> S" "0 \<le> G" "t \<in> {0..T}"
  shows "0 \<le> ramp_env S G T t"
  unfolding ramp_env_def using assms by simp

text \<open>The envelope integral J(T) = int m\<^latex>\<open>\textsuperscript{2}\<close>: S\<^latex>\<open>\textsuperscript{2}\<close> T\<^latex>\<open>\textsuperscript{3}\<close>/12 when the envelope is triangular
(S T <= 2 G), and G\<^latex>\<open>\textsuperscript{2}\<close> T - 4 G\<^latex>\<open>\textsuperscript{3}\<close>/(3 S) when it is trapezoidal.\<close>

definition ramp_J :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "ramp_J S G T = (if S * T \<le> 2 * G then S\<^sup>2 * T ^ 3 / 12 else G\<^sup>2 * T - 4 * G ^ 3 / (3 * S))"

lemma poly_int:
  fixes c a b :: real
  assumes "a \<le> b"
  shows "((\<lambda>t. c * t\<^sup>2) has_integral c * b ^ 3 / 3 - c * a ^ 3 / 3) {a..b}"
proof -
  have "\<And>x. ((\<lambda>t. c * t ^ 3 / 3) has_real_derivative c * x\<^sup>2) (at x)"
    by (auto intro!: derivative_eq_intros simp: power2_eq_square)
  thus ?thesis using ftc_real[OF assms, where F = "\<lambda>t. c * t ^ 3 / 3" and f = "\<lambda>t. c * t\<^sup>2"] by simp
qed

lemma poly_int_rev:
  fixes c a b T :: real
  assumes "a \<le> b"
  shows "((\<lambda>t. c * (T - t)\<^sup>2) has_integral c * (T - a) ^ 3 / 3 - c * (T - b) ^ 3 / 3) {a..b}"
proof -
  have "\<And>x. ((\<lambda>t. - (c * (T - t) ^ 3 / 3)) has_real_derivative c * (T - x)\<^sup>2) (at x)"
    by (auto intro!: derivative_eq_intros simp: power2_eq_square)
  thus ?thesis using ftc_real[OF assms, where F = "\<lambda>t. - (c * (T - t) ^ 3 / 3)" and f = "\<lambda>t. c * (T - t)\<^sup>2"] by simp
qed

theorem ramp_J_integral:
  fixes S G T :: real
  assumes S: "0 < S" and G: "0 < G" and T: "0 < T"
  shows "((\<lambda>t. (ramp_env S G T t)\<^sup>2) has_integral ramp_J S G T) {0..T}"
proof (cases "S * T \<le> 2 * G")
  case True
  have p1: "((\<lambda>t. S\<^sup>2 * t\<^sup>2) has_integral S\<^sup>2 * (T / 2) ^ 3 / 3) {0..T / 2}"
    using poly_int[where c = "S\<^sup>2" and a = 0 and b = "T / 2"] T by simp
  have i1: "((\<lambda>t. (ramp_env S G T t)\<^sup>2) has_integral S\<^sup>2 * (T / 2) ^ 3 / 3) {0..T / 2}"
  proof (rule has_integral_eq[OF _ p1])
    fix t assume t: "t \<in> {0..T / 2}"
    have "S * t \<le> S * (T - t)" using t S by (intro mult_left_mono) auto
    moreover have "S * t \<le> G"
    proof -
      have "S * t \<le> S * (T / 2)" using t S by (intro mult_left_mono) auto
      moreover have "S * (T / 2) = S * T / 2" by simp
      ultimately show ?thesis using True by linarith
    qed
    ultimately show "S\<^sup>2 * t\<^sup>2 = (ramp_env S G T t)\<^sup>2"
      unfolding ramp_env_def by (simp add: power_mult_distrib)
  qed
  have p2: "((\<lambda>t. S\<^sup>2 * (T - t)\<^sup>2) has_integral S\<^sup>2 * (T / 2) ^ 3 / 3) {T / 2..T}"
    using poly_int_rev[where c = "S\<^sup>2" and T = T and a = "T / 2" and b = T] T by simp
  have i2: "((\<lambda>t. (ramp_env S G T t)\<^sup>2) has_integral S\<^sup>2 * (T / 2) ^ 3 / 3) {T / 2..T}"
  proof (rule has_integral_eq[OF _ p2])
    fix t assume t: "t \<in> {T / 2..T}"
    have "S * (T - t) \<le> S * t" using t S by (intro mult_left_mono) auto
    moreover have "S * (T - t) \<le> G"
    proof -
      have "S * (T - t) \<le> S * (T / 2)" using t S by (intro mult_left_mono) auto
      moreover have "S * (T / 2) = S * T / 2" by simp
      ultimately show ?thesis using True by linarith
    qed
    ultimately show "S\<^sup>2 * (T - t)\<^sup>2 = (ramp_env S G T t)\<^sup>2"
      unfolding ramp_env_def by (simp add: power_mult_distrib)
  qed
  have "((\<lambda>t. (ramp_env S G T t)\<^sup>2) has_integral S\<^sup>2 * (T / 2) ^ 3 / 3 + S\<^sup>2 * (T / 2) ^ 3 / 3) {0..T}"
    by (rule has_integral_combine[OF _ _ i1 i2]) (use T in simp_all)
  moreover have "S\<^sup>2 * (T / 2) ^ 3 / 3 + S\<^sup>2 * (T / 2) ^ 3 / 3 = ramp_J S G T"
    unfolding ramp_J_def using True by (simp add: field_simps power3_eq_cube)
  ultimately show ?thesis by simp
next
  case False
  define u where "u = G / S"
  have u0: "0 < u" unfolding u_def using S G by simp
  have Su: "S * u = G" unfolding u_def using S by simp
  have uT: "2 * u < T"
  proof -
    have "S * (2 * u) = 2 * G" using Su by simp
    hence "S * (2 * u) < S * T" using False by linarith
    thus ?thesis using S by (simp add: mult_less_cancel_left_pos)
  qed
  have p1: "((\<lambda>t. S\<^sup>2 * t\<^sup>2) has_integral S\<^sup>2 * u ^ 3 / 3) {0..u}"
    using poly_int[where c = "S\<^sup>2" and a = 0 and b = u] u0 by simp
  have i1: "((\<lambda>t. (ramp_env S G T t)\<^sup>2) has_integral S\<^sup>2 * u ^ 3 / 3) {0..u}"
  proof (rule has_integral_eq[OF _ p1])
    fix t assume t: "t \<in> {0..u}"
    have "S * t \<le> S * (T - t)" using t S uT by (intro mult_left_mono) auto
    moreover have "S * t \<le> G"
    proof -
      have "S * t \<le> S * u" using t S by (intro mult_left_mono) auto
      thus ?thesis using Su by simp
    qed
    ultimately show "S\<^sup>2 * t\<^sup>2 = (ramp_env S G T t)\<^sup>2"
      unfolding ramp_env_def by (simp add: power_mult_distrib)
  qed
  have uu: "u \<le> T - u" using uT by simp
  have p2: "((\<lambda>t. G\<^sup>2) has_integral G\<^sup>2 * (T - u - u)) {u..T - u}"
  proof -
    have "((\<lambda>t. G\<^sup>2) has_integral G\<^sup>2 * (T - u) - G\<^sup>2 * u) {u..T - u}"
      by (rule ftc_real[OF uu, where F = "\<lambda>t. G\<^sup>2 * t"]) (auto intro!: derivative_eq_intros)
    thus ?thesis by (simp add: algebra_simps)
  qed
  have i2: "((\<lambda>t. (ramp_env S G T t)\<^sup>2) has_integral G\<^sup>2 * (T - u - u)) {u..T - u}"
  proof (rule has_integral_eq[OF _ p2])
    fix t assume t: "t \<in> {u..T - u}"
    have "S * u \<le> S * t" using t S by (intro mult_left_mono) auto
    hence "G \<le> S * t" using Su by simp
    moreover have "G \<le> S * (T - t)"
    proof -
      have "S * u \<le> S * (T - t)" using t S by (intro mult_left_mono) auto
      thus ?thesis using Su by simp
    qed
    ultimately show "G\<^sup>2 = (ramp_env S G T t)\<^sup>2" unfolding ramp_env_def by simp
  qed
  have p3: "((\<lambda>t. S\<^sup>2 * (T - t)\<^sup>2) has_integral S\<^sup>2 * u ^ 3 / 3) {T - u..T}"
    using poly_int_rev[where c = "S\<^sup>2" and T = T and a = "T - u" and b = T] u0 by simp
  have i3: "((\<lambda>t. (ramp_env S G T t)\<^sup>2) has_integral S\<^sup>2 * u ^ 3 / 3) {T - u..T}"
  proof (rule has_integral_eq[OF _ p3])
    fix t assume t: "t \<in> {T - u..T}"
    have "S * (T - t) \<le> S * t" using t S uT by (intro mult_left_mono) auto
    moreover have "S * (T - t) \<le> G"
    proof -
      have "S * (T - t) \<le> S * u" using t S by (intro mult_left_mono) auto
      thus ?thesis using Su by simp
    qed
    ultimately show "S\<^sup>2 * (T - t)\<^sup>2 = (ramp_env S G T t)\<^sup>2"
      unfolding ramp_env_def by (simp add: power_mult_distrib)
  qed
  have i12: "((\<lambda>t. (ramp_env S G T t)\<^sup>2) has_integral S\<^sup>2 * u ^ 3 / 3 + G\<^sup>2 * (T - u - u)) {0..T - u}"
    by (rule has_integral_combine[OF _ _ i1 i2]) (use u0 uT in simp_all)
  have tot: "((\<lambda>t. (ramp_env S G T t)\<^sup>2) has_integral
               S\<^sup>2 * u ^ 3 / 3 + G\<^sup>2 * (T - u - u) + S\<^sup>2 * u ^ 3 / 3) {0..T}"
    by (rule has_integral_combine[OF _ _ i12 i3]) (use u0 uT in simp_all)
  have "S\<^sup>2 * u ^ 3 / 3 + G\<^sup>2 * (T - u - u) + S\<^sup>2 * u ^ 3 / 3 = G\<^sup>2 * T - 4 * G ^ 3 / (3 * S)"
    unfolding u_def using S by (simp add: field_simps power3_eq_cube power2_eq_square)
  thus ?thesis using tot False unfolding ramp_J_def by simp
qed

lemma ramp_J_pos:
  assumes S: "0 < S" and G: "0 < G" and T: "0 < T"
  shows "0 < ramp_J S G T"
proof (cases "S * T \<le> 2 * G")
  case True
  thus ?thesis unfolding ramp_J_def using S T by simp
next
  case False
  hence "2 * G / S < T" using S by (simp add: divide_less_eq mult.commute)
  moreover have "4 * G / (3 * S) = (2 / 3) * (2 * G / S)" using S by (simp add: field_simps)
  moreover have "0 < 2 * G / S" using S G by simp
  ultimately have "4 * G / (3 * S) < T" by linarith
  hence "G\<^sup>2 * (4 * G / (3 * S)) < G\<^sup>2 * T" using G by (intro mult_strict_left_mono) auto
  moreover have "G\<^sup>2 * (4 * G / (3 * S)) = 4 * G ^ 3 / (3 * S)" by (simp add: power2_eq_square power3_eq_cube)
  ultimately have "0 < G\<^sup>2 * T - 4 * G ^ 3 / (3 * S)" by linarith
  thus ?thesis unfolding ramp_J_def using False by simp
qed

text \<open>The floor for ramped couplings: if the receiver's coupling g changes at slope at most S, starts and
ends at zero and is bounded by G, and |z'| <= |g(t)| y, then z(T)\<^latex>\<open>\textsuperscript{2}\<close> (1 + delta / J(T)) <= 1.\<close>

theorem ramp_loss_floor:
  fixes n y z n' z' :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> 'a::real_normed_vector"
    and S G T \<delta> :: real and E :: "real set"
  assumes S: "0 < S" and G: "0 < G" and T: "0 < T" and d0: "0 \<le> \<delta>" and E: "countable E"
    and nc: "continuous_on {0..T} n" and yc: "continuous_on {0..T} y" and zc: "continuous_on {0..T} z"
    and y0: "\<forall>t\<in>{0..T}. 0 \<le> y t"
    and lip: "\<forall>s\<in>{0..T}. \<forall>t\<in>{0..T}. norm (g s - g t) \<le> S * \<bar>s - t\<bar>"
    and g0: "g 0 = 0" and gT: "g T = 0" and gG: "\<forall>t\<in>{0..T}. norm (g t) \<le> G"
    and n0: "n 0 \<le> 1" and z0: "z 0 = 0" and zT: "(z T)\<^sup>2 \<le> n T"
    and der: "\<forall>t\<in>{0<..<T} - E. (n has_real_derivative n' t) (at t) \<and> (z has_real_derivative z' t) (at t)"
    and bnd: "\<forall>t\<in>{0<..<T} - E. n' t \<le> - \<delta> * (y t)\<^sup>2 \<and> \<bar>z' t\<bar> \<le> norm (g t) * y t"
  shows "(z T)\<^sup>2 * (1 + \<delta> / ramp_J S G T) \<le> 1"
proof -
  have Jeq: "integral {0..T} (\<lambda>t. (ramp_env S G T t)\<^sup>2) = ramp_J S G T"
    using ramp_J_integral[OF S G T] by (rule integral_unique)
  have bnd': "\<forall>t\<in>{0<..<T} - E. n' t \<le> - \<delta> * (y t)\<^sup>2 \<and> \<bar>z' t\<bar> \<le> ramp_env S G T t * y t"
  proof
    fix t assume t: "t \<in> {0<..<T} - E"
    hence tc: "t \<in> {0..T}" by auto
    have "norm (g t) * y t \<le> ramp_env S G T t * y t"
      by (rule mult_right_mono[OF ramp_envelope[OF lip g0 gT gG tc]]) (use y0 tc in blast)
    moreover have "n' t \<le> - \<delta> * (y t)\<^sup>2" and "\<bar>z' t\<bar> \<le> norm (g t) * y t" using bnd t by auto
    ultimately show "n' t \<le> - \<delta> * (y t)\<^sup>2 \<and> \<bar>z' t\<bar> \<le> ramp_env S G T t * y t" by linarith
  qed
  have "(z T)\<^sup>2 * (1 + \<delta> / integral {0..T} (\<lambda>t. (ramp_env S G T t)\<^sup>2)) \<le> 1"
    by (rule weighted_loss_floor[OF T d0 E nc yc zc ramp_env_cont _ y0 _ n0 z0 zT der bnd'])
       (use ramp_env_nonneg S G Jeq ramp_J_pos[OF S G T] in auto)
  thus ?thesis unfolding Jeq .
qed

section \<open>A closed-form estimate at every duration\<close>

text \<open>Since exp(-u) <= 1/(1 + u) and by the inequality of arithmetic and geometric means, the floor
exp(-gamma T) / (1 + delta/(G\<^latex>\<open>\textsuperscript{2}\<close> T)) is at most (1 + sqrt(gamma delta)/G)\<^latex>\<open>\textsuperscript{-2}\<close> at every T.\<close>

theorem floor_closed_estimate:
  fixes \<gamma> \<delta> G T :: real
  assumes g: "0 \<le> \<gamma>" and d: "0 \<le> \<delta>" and G: "0 < G" and T: "0 < T"
  shows "exp (- \<gamma> * T) / (1 + \<delta> / (G\<^sup>2 * T)) \<le> 1 / (1 + sqrt (\<gamma> * \<delta>) / G)\<^sup>2"
proof -
  define p where "p = sqrt (\<gamma> * T)"
  define q where "q = sqrt (\<delta> / (G\<^sup>2 * T))"
  have p2: "p\<^sup>2 = \<gamma> * T" unfolding p_def using g T by simp
  have q2: "q\<^sup>2 = \<delta> / (G\<^sup>2 * T)" unfolding q_def using d G T by simp
  have pq: "p * q = sqrt (\<gamma> * \<delta>) / G"
  proof -
    have "p * q = sqrt (\<gamma> * T * (\<delta> / (G\<^sup>2 * T)))" unfolding p_def q_def by (rule real_sqrt_mult[symmetric])
    also have "\<gamma> * T * (\<delta> / (G\<^sup>2 * T)) = (\<gamma> * \<delta>) / G\<^sup>2" using T by (simp add: field_simps)
    also have "sqrt \<dots> = sqrt (\<gamma> * \<delta>) / G" using G by (simp add: real_sqrt_divide)
    finally show ?thesis .
  qed
  have e: "exp (- \<gamma> * T) \<le> 1 / (1 + \<gamma> * T)"
  proof -
    have "1 + \<gamma> * T \<le> exp (\<gamma> * T)" by (rule exp_ge_add_one_self)
    moreover have "0 < 1 + \<gamma> * T"
    proof -
      have "0 \<le> \<gamma> * T" using g T by simp
      thus ?thesis by linarith
    qed
    ultimately have "inverse (exp (\<gamma> * T)) \<le> inverse (1 + \<gamma> * T)" by (rule le_imp_inverse_le)
    thus ?thesis by (simp add: exp_minus inverse_eq_divide)
  qed
  have amgm: "(1 + p * q)\<^sup>2 \<le> (1 + p\<^sup>2) * (1 + q\<^sup>2)"
  proof -
    have "(1 + p\<^sup>2) * (1 + q\<^sup>2) - (1 + p * q)\<^sup>2 = (p - q)\<^sup>2" by (simp add: power2_eq_square algebra_simps)
    moreover have "0 \<le> (p - q)\<^sup>2" by simp
    ultimately show ?thesis by linarith
  qed
  have pos1: "0 < 1 + \<delta> / (G\<^sup>2 * T)" using d G T by (simp add: add_pos_nonneg)
  have pos2: "0 < (1 + p * q)\<^sup>2"
  proof -
    have "0 \<le> p * q" unfolding pq using g d G by simp
    hence "0 < 1 + p * q" by linarith
    thus ?thesis by simp
  qed
  have "exp (- \<gamma> * T) / (1 + \<delta> / (G\<^sup>2 * T)) \<le> (1 / (1 + \<gamma> * T)) / (1 + \<delta> / (G\<^sup>2 * T))"
    by (rule divide_right_mono[OF e less_imp_le[OF pos1]])
  also have "\<dots> = 1 / ((1 + p\<^sup>2) * (1 + q\<^sup>2))" using p2 q2 by simp
  also have "\<dots> \<le> 1 / (1 + p * q)\<^sup>2"
  proof -
    have pos3: "0 < (1 + p\<^sup>2) * (1 + q\<^sup>2)" by (intro mult_pos_pos) (simp_all add: add_pos_nonneg)
    show ?thesis by (rule divide_left_mono[OF amgm]) (use mult_pos_pos[OF pos3 pos2] in simp_all)
  qed
  finally show ?thesis unfolding pq .
qed

section \<open>The receiver's bus term with an excess rate\<close>

text \<open>JB(T) = (1 - exp(-d T))/d (and T when d = 0) is the integral of exp(-d (T - t)) over [0, T].\<close>

definition JB :: "real \<Rightarrow> real \<Rightarrow> real" where
  "JB d T = (if d = 0 then T else (1 - exp (- d * T)) / d)"

lemma JB_integral:
  fixes d T :: real
  assumes T: "0 \<le> T"
  shows "((\<lambda>t. exp (- d * (T - t))) has_integral JB d T) {0..T}"
proof (cases "d = 0")
  case True
  have "((\<lambda>t. 1) has_integral T - 0) {0..T}"
    by (rule ftc_real[OF T, where F = "\<lambda>t. t"]) (auto intro!: derivative_eq_intros)
  thus ?thesis unfolding JB_def using True by simp
next
  case False
  have "\<And>x. ((\<lambda>t. exp (- d * (T - t)) / d) has_real_derivative exp (- d * (T - x))) (at x)"
    using False by (auto intro!: derivative_eq_intros simp: field_simps)
  hence "((\<lambda>t. exp (- d * (T - t))) has_integral exp (- d * (T - T)) / d - exp (- d * (T - 0)) / d) {0..T}"
    by (rule ftc_real[OF T])
  thus ?thesis unfolding JB_def using False by (simp add: diff_divide_distrib)
qed

lemma JB_pos:
  assumes d: "0 \<le> d" and T: "0 < T"
  shows "0 < JB d T"
proof (cases "d = 0")
  case True
  thus ?thesis unfolding JB_def using T by simp
next
  case False
  hence d0: "0 < d" using d by simp
  have "exp (- d * T) < 1" using d0 T by simp
  thus ?thesis unfolding JB_def using False d0 by simp
qed

text \<open>With z' <= G y - (d/2) z (a receiver that loses at the excess rate d) and z(0) = 0, the delivered
amplitude is at most G times the integral of exp(-d (T - t)/2) y.\<close>

lemma bus_window:
  fixes z z' y :: "real \<Rightarrow> real" and G d T :: real and S :: "real set"
  assumes T: "0 < T" and S: "countable S"
    and zc: "continuous_on {0..T} z" and yc: "continuous_on {0..T} y" and z0: "z 0 = 0"
    and der: "\<forall>t\<in>{0<..<T} - S. (z has_real_derivative z' t) (at t) \<and> z' t \<le> G * y t - d / 2 * z t"
  shows "z T \<le> integral {0..T} (\<lambda>t. G * exp (- d * (T - t) / 2) * y t)"
proof -
  define u where "u = (\<lambda>t. exp (d * t / 2) * z t)"
  define h where "h = (\<lambda>t. G * exp (d * t / 2) * y t)"
  have uc: "continuous_on {0..T} u" unfolding u_def using zc by (intro continuous_intros) auto
  have hc: "continuous_on {0..T} h" unfolding h_def using yc by (intro continuous_intros) auto
  have du: "(u has_real_derivative (exp (d * t / 2) * (d / 2)) * z t + exp (d * t / 2) * z' t) (at t)
            \<and> (exp (d * t / 2) * (d / 2)) * z t + exp (d * t / 2) * z' t \<le> h t"
    if t: "t \<in> {0<..<T} - S" for t
  proof
    have dz: "(z has_real_derivative z' t) (at t)" using der t by blast
    have de: "((\<lambda>t. exp (d * t / 2)) has_real_derivative exp (d * t / 2) * (d / 2)) (at t)"
      by (auto intro!: derivative_eq_intros)
    show "(u has_real_derivative (exp (d * t / 2) * (d / 2)) * z t + exp (d * t / 2) * z' t) (at t)"
      unfolding u_def using DERIV_mult[OF de dz] by (simp add: algebra_simps)
    have "z' t \<le> G * y t - d / 2 * z t" using der t by blast
    hence "exp (d * t / 2) * (d / 2 * z t + z' t) \<le> exp (d * t / 2) * (G * y t)"
      by (intro mult_left_mono) auto
    thus "(exp (d * t / 2) * (d / 2)) * z t + exp (d * t / 2) * z' t \<le> h t"
      unfolding h_def by (simp add: algebra_simps)
  qed
  have "u T - u 0 \<le> integral {0..T} h" by (rule ftc_le[OF S less_imp_le[OF T] uc hc du])
  hence uT: "exp (d * T / 2) * z T \<le> integral {0..T} h" unfolding u_def using z0 by simp
  have hi: "(h has_integral integral {0..T} h) {0..T}"
    using integrable_continuous_real[OF hc] by (rule integrable_integral)
  have ki: "((\<lambda>t. G * exp (- d * (T - t) / 2) * y t) has_integral exp (- d * T / 2) * integral {0..T} h) {0..T}"
  proof (rule has_integral_eq[OF _ has_integral_mult_right[OF hi]])
    fix t
    have "exp (- d * T / 2) * exp (d * t / 2) = exp (- d * (T - t) / 2)"
      by (simp add: exp_add[symmetric] algebra_simps diff_divide_distrib)
    thus "exp (- d * T / 2) * h t = G * exp (- d * (T - t) / 2) * y t"
      unfolding h_def by (metis mult.assoc mult.left_commute)
  qed
  have "z T = exp (- d * T / 2) * (exp (d * T / 2) * z T)" by (simp add: exp_minus field_simps)
  also have "\<dots> \<le> exp (- d * T / 2) * integral {0..T} h" using uT by (simp add: mult_left_mono)
  also have "\<dots> = integral {0..T} (\<lambda>t. G * exp (- d * (T - t) / 2) * y t)" using ki by (simp add: integral_unique)
  finally show ?thesis .
qed

text \<open>The bus term: (z T)\<^latex>\<open>\textsuperscript{2}\<close> <= G\<^latex>\<open>\textsuperscript{2}\<close> JB(T) int y\<^latex>\<open>\textsuperscript{2}\<close>, that is, int y\<^latex>\<open>\textsuperscript{2}\<close> >= z(T)\<^latex>\<open>\textsuperscript{2}\<close> / (G\<^latex>\<open>\textsuperscript{2}\<close> JB(T)).\<close>

theorem bus_term:
  fixes z z' y :: "real \<Rightarrow> real" and G d T :: real and S :: "real set"
  assumes T: "0 < T" and S: "countable S"
    and zc: "continuous_on {0..T} z" and yc: "continuous_on {0..T} y" and z0: "z 0 = 0"
    and zTn: "0 \<le> z T"
    and der: "\<forall>t\<in>{0<..<T} - S. (z has_real_derivative z' t) (at t) \<and> z' t \<le> G * y t - d / 2 * z t"
  shows "(z T)\<^sup>2 \<le> G\<^sup>2 * JB d T * integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
proof -
  define m where "m = (\<lambda>t. G * exp (- d * (T - t) / 2))"
  have mc: "continuous_on {0..T} m" unfolding m_def by (intro continuous_intros) auto
  have b: "z T \<le> integral {0..T} (\<lambda>t. m t * y t)"
    using bus_window[OF T S zc yc z0 der] unfolding m_def .
  have m2: "(m t)\<^sup>2 = G\<^sup>2 * exp (- d * (T - t))" for t
  proof -
    have "(exp (- d * (T - t) / 2))\<^sup>2 = exp (- d * (T - t) / 2 + - d * (T - t) / 2)"
      by (simp only: power2_eq_square exp_add)
    also have "- d * (T - t) / 2 + - d * (T - t) / 2 = - d * (T - t)" by simp
    finally have e2: "(exp (- d * (T - t) / 2))\<^sup>2 = exp (- d * (T - t))" .
    show ?thesis unfolding m_def power_mult_distrib e2 by (rule refl)
  qed
  have "((\<lambda>t. (m t)\<^sup>2) has_integral G\<^sup>2 * JB d T) {0..T}"
    unfolding m2 by (rule has_integral_mult_right[OF JB_integral]) (use T in simp)
  hence Mi: "integral {0..T} (\<lambda>t. (m t)\<^sup>2) = G\<^sup>2 * JB d T" by (rule integral_unique)
  have "(z T)\<^sup>2 \<le> (integral {0..T} (\<lambda>t. m t * y t))\<^sup>2" using b zTn by (simp add: power_mono)
  also have "\<dots> \<le> integral {0..T} (\<lambda>t. (m t)\<^sup>2) * integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
    by (rule cauchy_schwarz_weighted[OF less_imp_le[OF T] mc yc])
  finally show ?thesis unfolding Mi .
qed

section \<open>The norm balance with an excess rate per element\<close>

text \<open>With excess rates dA, dC, dB >= 0 of the emitter, the bus and the receiver, the norm obeys
n' <= -dA x\<^latex>\<open>\textsuperscript{2}\<close> - dC y\<^latex>\<open>\textsuperscript{2}\<close> - dB z\<^latex>\<open>\textsuperscript{2}\<close> and the receiver z' <= G y - (dB/2) z. For any
lower bounds a <= int x\<^latex>\<open>\textsuperscript{2}\<close>, b <= int z\<^latex>\<open>\textsuperscript{2}\<close> (the emitter and receiver windows) and any
0 <= f <= x(T), the delivered amplitude zeta = z(T) satisfies
zeta\<^latex>\<open>\textsuperscript{2}\<close> + f\<^latex>\<open>\textsuperscript{2}\<close> + dA a + dB b + dC zeta\<^latex>\<open>\textsuperscript{2}\<close> / (G\<^latex>\<open>\textsuperscript{2}\<close> JB(T)) <= 1.\<close>

theorem windows_balance:
  fixes n x y z n' z' :: "real \<Rightarrow> real" and G T dA dB dC f a b :: real and S :: "real set"
  assumes T: "0 < T" and G: "0 < G" and dA: "0 \<le> dA" and dB: "0 \<le> dB" and dC: "0 \<le> dC"
    and S: "countable S"
    and nc: "continuous_on {0..T} n" and xc: "continuous_on {0..T} x"
    and yc: "continuous_on {0..T} y" and zc: "continuous_on {0..T} z"
    and zTn: "0 \<le> z T" and n0: "n 0 \<le> 1" and z0: "z 0 = 0"
    and der: "\<forall>t\<in>{0<..<T} - S. (n has_real_derivative n' t) (at t) \<and> (z has_real_derivative z' t) (at t)"
    and bnd: "\<forall>t\<in>{0<..<T} - S. n' t \<le> - dA * (x t)\<^sup>2 - dC * (y t)\<^sup>2 - dB * (z t)\<^sup>2
                                 \<and> z' t \<le> G * y t - dB / 2 * z t"
    and fin: "(x T)\<^sup>2 + (z T)\<^sup>2 \<le> n T"
    and f0: "0 \<le> f" and fx: "f \<le> x T"
    and a: "a \<le> integral {0..T} (\<lambda>t. (x t)\<^sup>2)" and b: "b \<le> integral {0..T} (\<lambda>t. (z t)\<^sup>2)"
  shows "(z T)\<^sup>2 + f\<^sup>2 + dA * a + dB * b + dC * (z T)\<^sup>2 / (G\<^sup>2 * JB dB T) \<le> 1"
proof -
  define X where "X = integral {0..T} (\<lambda>t. (x t)\<^sup>2)"
  define Y where "Y = integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
  define Z where "Z = integral {0..T} (\<lambda>t. (z t)\<^sup>2)"
  have x2c: "continuous_on {0..T} (\<lambda>t. (x t)\<^sup>2)" using xc by (intro continuous_intros)
  have y2c: "continuous_on {0..T} (\<lambda>t. (y t)\<^sup>2)" using yc by (intro continuous_intros)
  have z2c: "continuous_on {0..T} (\<lambda>t. (z t)\<^sup>2)" using zc by (intro continuous_intros)
  have hc: "continuous_on {0..T} (\<lambda>t. - dA * (x t)\<^sup>2 - dC * (y t)\<^sup>2 - dB * (z t)\<^sup>2)"
    using xc yc zc by (intro continuous_intros)
  have "n T - n 0 \<le> integral {0..T} (\<lambda>t. - dA * (x t)\<^sup>2 - dC * (y t)\<^sup>2 - dB * (z t)\<^sup>2)"
    by (rule ftc_le[OF S less_imp_le[OF T] nc hc]) (use der bnd in blast)
  also have "\<dots> = - dA * X - dC * Y - dB * Z"
  proof -
    have Xi: "((\<lambda>t. (x t)\<^sup>2) has_integral X) {0..T}" unfolding X_def
      using integrable_continuous_real[OF x2c] by (rule integrable_integral)
    have Yi: "((\<lambda>t. (y t)\<^sup>2) has_integral Y) {0..T}" unfolding Y_def
      using integrable_continuous_real[OF y2c] by (rule integrable_integral)
    have Zi: "((\<lambda>t. (z t)\<^sup>2) has_integral Z) {0..T}" unfolding Z_def
      using integrable_continuous_real[OF z2c] by (rule integrable_integral)
    have "((\<lambda>t. - dA * (x t)\<^sup>2 - dC * (y t)\<^sup>2 - dB * (z t)\<^sup>2) has_integral - dA * X - dC * Y - dB * Z) {0..T}"
      by (rule has_integral_diff[OF has_integral_diff[OF has_integral_mult_right[OF Xi]
            has_integral_mult_right[OF Yi]] has_integral_mult_right[OF Zi]])
    thus ?thesis by (rule integral_unique)
  qed
  finally have nb: "n T \<le> 1 - dA * X - dC * Y - dB * Z" using n0 by linarith
  have JB0: "0 < JB dB T" by (rule JB_pos[OF dB T])
  have GJ: "0 < G\<^sup>2 * JB dB T" using G JB0 by simp
  have bt: "(z T)\<^sup>2 \<le> G\<^sup>2 * JB dB T * Y" unfolding Y_def
    by (rule bus_term[where z' = z', OF T S zc yc z0 zTn]) (use der bnd in blast)
  have Yb: "(z T)\<^sup>2 / (G\<^sup>2 * JB dB T) \<le> Y" using bt GJ by (simp add: divide_le_eq mult.commute)
  have f2: "f\<^sup>2 \<le> (x T)\<^sup>2" using f0 fx by (simp add: power_mono)
  have "dA * a \<le> dA * X" using a dA unfolding X_def by (rule mult_left_mono)
  moreover have "dB * b \<le> dB * Z" using b dB unfolding Z_def by (rule mult_left_mono)
  moreover have "dC * ((z T)\<^sup>2 / (G\<^sup>2 * JB dB T)) \<le> dC * Y" using Yb dC by (rule mult_left_mono)
  ultimately show ?thesis using nb fin f2 by simp
qed

end
