(*  Title:      Relay_Occupation.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Lower bound (1 - eps) / (G^2 T) on the integrated occupation of the bus for any control, and the
    time--occupation frontier 2u <= G^2 T * integral of the occupation.
*)
theory Relay_Occupation
  imports Relay_Dephasing
begin

text \<open>Two results on the occupation of the bus mode during a relay with bounded couplings |g| <= G: a lower bound on the integrated occupation, valid for any control, and the time--occupation frontier. The fundamental-theorem lemma of the dephasing theory is reused.\<close>

section \<open>Auxiliary lemmas\<close>

lemma cauchy_schwarz_cont:
  fixes y :: "real \<Rightarrow> real" and T :: real
  assumes "0 < T" "continuous_on {0..T} y"
  shows "(integral {0..T} y)\<^sup>2 \<le> T * integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
proof -
  define I where "I = integral {0..T} y"
  define J where "J = integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
  define c where "c = I / T"
  have yi: "(y has_integral I) {0..T}" unfolding I_def
    using integrable_continuous_real[OF assms(2)] by (rule integrable_integral)
  have y2c: "continuous_on {0..T} (\<lambda>t. (y t)\<^sup>2)" using assms(2) by (intro continuous_intros)
  have y2i: "((\<lambda>t. (y t)\<^sup>2) has_integral J) {0..T}" unfolding J_def
    using integrable_continuous_real[OF y2c] by (rule integrable_integral)
  have ci: "((\<lambda>t. c\<^sup>2) has_integral c\<^sup>2 * T) {0..T}"
    using has_integral_const_real[of "c\<^sup>2" 0 T] assms(1) by (simp add: mult.commute)
  have yci: "((\<lambda>t. (2 * c) * y t) has_integral (2 * c) * I) {0..T}"
    using has_integral_mult_right[OF yi, of "2 * c"] by simp
  have tot: "((\<lambda>t. (y t)\<^sup>2 - (2 * c) * y t + c\<^sup>2) has_integral J - (2 * c) * I + c\<^sup>2 * T) {0..T}"
    by (rule has_integral_add[OF has_integral_diff[OF y2i yci] ci])
  have nn: "0 \<le> J - (2 * c) * I + c\<^sup>2 * T"
  proof (rule has_integral_nonneg[OF tot])
    fix t assume "t \<in> {0..T}"
    have "(y t)\<^sup>2 - (2 * c) * y t + c\<^sup>2 = (y t - c)\<^sup>2" by (simp add: power2_eq_square algebra_simps)
    thus "0 \<le> (y t)\<^sup>2 - (2 * c) * y t + c\<^sup>2" by simp
  qed
  have "J - (2 * c) * I + c\<^sup>2 * T = J - I\<^sup>2 / T"
    unfolding c_def using assms(1) by (simp add: field_simps power2_eq_square)
  hence "I\<^sup>2 / T \<le> J" using nn by simp
  thus ?thesis unfolding I_def J_def using assms(1) by (simp add: field_simps)
qed

text \<open>Fundamental theorem of calculus with countably many exceptions: |F b - F a| is bounded by the integral of a continuous majorant of |F'|.\<close>

lemma ftc_bound:
  fixes F F' g :: "real \<Rightarrow> real" and a b :: real and S :: "real set"
  assumes S: "countable S" and ab: "a \<le> b"
    and Fc: "continuous_on {a..b} F" and gc: "continuous_on {a..b} g"
    and g0: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> g t"
    and der: "\<And>t. t \<in> {a<..<b} - S \<Longrightarrow> (F has_real_derivative F' t) (at t) \<and> \<bar>F' t\<bar> \<le> g t"
  shows "\<bar>F b - F a\<bar> \<le> integral {a..b} g"
proof -
  define f where "f = (\<lambda>t. if t \<in> {a<..<b} - S then F' t else 0)"
  have fd: "\<And>t. t \<in> {a<..<b} - S \<Longrightarrow> (F has_vector_derivative f t) (at t)"
  proof -
    fix t assume t: "t \<in> {a<..<b} - S"
    have "f t = F' t" unfolding f_def using t by simp
    thus "(F has_vector_derivative f t) (at t)" using der[OF t] by (simp add: has_real_derivative_iff_has_vector_derivative)
  qed
  have ftc: "(f has_integral F b - F a) {a..b}"
    by (rule fundamental_theorem_of_calculus_interior_strong[OF S ab fd Fc])
  define I where "I = integral {a..b} g"
  have gi: "(g has_integral I) {a..b}" unfolding I_def
    using integrable_continuous_real[OF gc] by (rule integrable_integral)
  have fle: "\<And>t. t \<in> {a..b} \<Longrightarrow> f t \<le> g t"
  proof -
    fix t assume t: "t \<in> {a..b}"
    show "f t \<le> g t"
    proof (cases "t \<in> {a<..<b} - S")
      case True
      hence "f t = F' t" unfolding f_def by (rule if_P)
      thus ?thesis using der[OF True] by (simp add: abs_le_iff)
    next
      case False
      hence "f t = 0" unfolding f_def by (rule if_not_P)
      thus ?thesis using g0[OF t] by simp
    qed
  qed
  have fge: "\<And>t. t \<in> {a..b} \<Longrightarrow> - f t \<le> g t"
  proof -
    fix t assume t: "t \<in> {a..b}"
    show "- f t \<le> g t"
    proof (cases "t \<in> {a<..<b} - S")
      case True
      hence "f t = F' t" unfolding f_def by (rule if_P)
      thus ?thesis using der[OF True] by (simp add: abs_le_iff)
    next
      case False
      hence "f t = 0" unfolding f_def by (rule if_not_P)
      thus ?thesis using g0[OF t] by simp
    qed
  qed
  have up: "F b - F a \<le> I" by (rule has_integral_le[OF ftc gi fle])
  have fneg: "((\<lambda>t. - f t) has_integral - (F b - F a)) {a..b}" by (rule has_integral_neg[OF ftc])
  have lo: "- (F b - F a) \<le> I" by (rule has_integral_le[OF fneg gi fge])
  show ?thesis unfolding I_def[symmetric] using up lo by (simp add: abs_le_iff)
qed

text \<open>Areas of the two half-triangles.\<close>

lemma tri_left:
  fixes M h tc w :: real
  assumes "0 < M" "0 \<le> w" "h = M * w"
  shows "((\<lambda>t. h - M * (tc - t)) has_integral h * w / 2) {tc - w..tc}"
proof -
  let ?F = "\<lambda>t::real. (h - M * tc) * t + M * t\<^sup>2 / 2"
  have "((\<lambda>t. h - M * (tc - t)) has_integral ?F tc - ?F (tc - w)) {tc - w..tc}"
  proof (rule ftc_real)
    show "tc - w \<le> tc" using assms(2) by simp
    fix t :: real
    have "(?F has_real_derivative (h - M * tc) + M * t) (at t)"
      by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square)
    moreover have "(h - M * tc) + M * t = h - M * (tc - t)" by (simp add: algebra_simps)
    ultimately show "(?F has_real_derivative h - M * (tc - t)) (at t)" by simp
  qed
  moreover have "?F tc - ?F (tc - w) = h * w / 2"
    using assms(3) by (simp add: power2_eq_square field_simps algebra_simps)
  ultimately show ?thesis by simp
qed

lemma tri_right:
  fixes M h tc w :: real
  assumes "0 < M" "0 \<le> w" "h = M * w"
  shows "((\<lambda>t. h - M * (t - tc)) has_integral h * w / 2) {tc..tc + w}"
proof -
  let ?F = "\<lambda>t::real. (h + M * tc) * t - M * t\<^sup>2 / 2"
  have "((\<lambda>t. h - M * (t - tc)) has_integral ?F (tc + w) - ?F tc) {tc..tc + w}"
  proof (rule ftc_real)
    show "tc \<le> tc + w" using assms(2) by simp
    fix t :: real
    have "(?F has_real_derivative (h + M * tc) - M * t) (at t)"
      by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square)
    moreover have "(h + M * tc) - M * t = h - M * (t - tc)" by (simp add: algebra_simps)
    ultimately show "(?F has_real_derivative h - M * (t - tc)) (at t)" by simp
  qed
  moreover have "?F (tc + w) - ?F tc = h * w / 2"
    using assms(3) by (simp add: power2_eq_square field_simps algebra_simps)
  ultimately show ?thesis by simp
qed

section \<open>Lower bound on the integrated occupation\<close>

text \<open>Lower bound on the integrated bus occupation. Here z is the amplitude of the target qubit, z 0 = 0 and (z T)\<^latex>\<open>\textsuperscript{2}\<close> >= 1 - eps (the transfer is complete up to the error eps), with |z'| <= G y, where y >= 0 is any continuous function (for the relay one takes y to be the square root of the bus occupation, y\<^latex>\<open>\textsuperscript{2}\<close> = 1 - x\<^latex>\<open>\textsuperscript{2}\<close> - z\<^latex>\<open>\textsuperscript{2}\<close>). Then the integral of y\<^latex>\<open>\textsuperscript{2}\<close> over [0, T] is at least (1 - eps) / (G\<^latex>\<open>\textsuperscript{2}\<close> T) for any control.\<close>

theorem occupation_lower_bound:
  fixes z z' y :: "real \<Rightarrow> real" and G T \<epsilon> :: real and S :: "real set"
  assumes T: "0 < T" and G: "0 < G" and eps: "0 \<le> \<epsilon>" "\<epsilon> \<le> 1"
    and zc: "continuous_on {0..T} z" and z0: "z 0 = 0" and zT: "(z T)\<^sup>2 \<ge> 1 - \<epsilon>"
    and S: "countable S"
    and der: "\<And>t. t \<in> {0<..<T} - S \<Longrightarrow> (z has_real_derivative z' t) (at t)"
    and bnd: "\<And>t. t \<in> {0<..<T} - S \<Longrightarrow> \<bar>z' t\<bar> \<le> G * y t"
    and yc: "continuous_on {0..T} y" and y0: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> y t"
  shows "(1 - \<epsilon>) / (G\<^sup>2 * T) \<le> integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
proof -
  define f where "f = (\<lambda>t. if t \<in> {0<..<T} - S then z' t else 0)"
  have ftc: "(f has_integral z T - z 0) {0..T}"
  proof -
    have fd: "\<And>t. t \<in> {0<..<T} - S \<Longrightarrow> (z has_vector_derivative f t) (at t)"
    proof -
      fix t assume t: "t \<in> {0<..<T} - S"
      have "f t = z' t" unfolding f_def using t by simp
      thus "(z has_vector_derivative f t) (at t)" using der[OF t] by (simp add: has_real_derivative_iff_has_vector_derivative)
    qed
    show ?thesis
      by (rule fundamental_theorem_of_calculus_interior_strong[OF S less_imp_le[OF T] fd zc])
  qed
  define I where "I = integral {0..T} y"
  have yi: "(y has_integral I) {0..T}" unfolding I_def
    using integrable_continuous_real[OF yc] by (rule integrable_integral)
  have Gy: "((\<lambda>t. G * y t) has_integral G * I) {0..T}" using has_integral_mult_right[OF yi, of G] by simp
  have fle: "\<And>t. t \<in> {0..T} \<Longrightarrow> f t \<le> G * y t"
  proof -
    fix t assume t: "t \<in> {0..T}"
    show "f t \<le> G * y t"
    proof (cases "t \<in> {0<..<T} - S")
      case True
      hence "f t = z' t" unfolding f_def by (rule if_P)
      thus ?thesis using bnd[OF True] by (simp add: abs_le_iff)
    next
      case False
      hence "f t = 0" unfolding f_def by (rule if_not_P)
      thus ?thesis using y0[OF t] G by simp
    qed
  qed
  have fge: "\<And>t. t \<in> {0..T} \<Longrightarrow> - f t \<le> G * y t"
  proof -
    fix t assume t: "t \<in> {0..T}"
    show "- f t \<le> G * y t"
    proof (cases "t \<in> {0<..<T} - S")
      case True
      hence "f t = z' t" unfolding f_def by (rule if_P)
      thus ?thesis using bnd[OF True] by (simp add: abs_le_iff)
    next
      case False
      hence "f t = 0" unfolding f_def by (rule if_not_P)
      thus ?thesis using y0[OF t] G by simp
    qed
  qed
  have up: "z T - z 0 \<le> G * I" by (rule has_integral_le[OF ftc Gy fle])
  have fneg: "((\<lambda>t. - f t) has_integral - (z T - z 0)) {0..T}" by (rule has_integral_neg[OF ftc])
  have lo: "- (z T - z 0) \<le> G * I" by (rule has_integral_le[OF fneg Gy fge])
  have "\<bar>z T\<bar> \<le> G * I" using up lo z0 by (simp add: abs_le_iff)
  hence sq: "(z T)\<^sup>2 \<le> (G * I)\<^sup>2" using power_mono[OF \<open>\<bar>z T\<bar> \<le> G * I\<close> abs_ge_zero, of 2] by simp
  have cs: "I\<^sup>2 \<le> T * integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
    unfolding I_def by (rule cauchy_schwarz_cont[OF T yc])
  have "1 - \<epsilon> \<le> G\<^sup>2 * (T * integral {0..T} (\<lambda>t. (y t)\<^sup>2))"
  proof -
    have "1 - \<epsilon> \<le> (G * I)\<^sup>2" using zT sq by linarith
    also have "... = G\<^sup>2 * I\<^sup>2" by (simp add: power_mult_distrib)
    also have "... \<le> G\<^sup>2 * (T * integral {0..T} (\<lambda>t. (y t)\<^sup>2))" by (rule mult_left_mono[OF cs]) (rule zero_le_power2)
    finally show ?thesis .
  qed
  thus ?thesis using G T by (simp add: pos_divide_le_eq algebra_simps)
qed

section \<open>The time--occupation frontier\<close>

text \<open>Same relay as in the minimal-time theory, with the bus occupation p = 1 - x\<^latex>\<open>\textsuperscript{2}\<close> - z\<^latex>\<open>\textsuperscript{2}\<close> integrated over the transfer, with x 0 = 1, z 0 = 0, x T = 0, z T = 1. If 0 <= u <= 1 and 2u <= G T (1 - u)\<^latex>\<open>\textsuperscript{2}\<close> / (2 sqrt 2), then 2u <= G\<^latex>\<open>\textsuperscript{2}\<close> T times the integral of p over [0, T].\<close>

theorem occupation_frontier:
  fixes x z x' z' :: "real \<Rightarrow> real" and G T u :: real and S :: "real set"
  assumes T: "0 < T" and G: "0 < G" and S: "countable S"
    and cx: "continuous_on {0..T} x" and cz: "continuous_on {0..T} z"
    and D: "\<forall>t\<in>{0..T}. 0 \<le> x t \<and> 0 \<le> z t \<and> (x t)\<^sup>2 + (z t)\<^sup>2 \<le> 1"
    and x0: "x 0 = 1" and z0: "z 0 = 0" and xT: "x T = 0" and zT: "z T = 1"
    and der: "\<forall>t\<in>{0<..<T} - S. (x has_real_derivative x' t) (at t) \<and> (z has_real_derivative z' t) (at t)"
    and bnd: "\<forall>t\<in>{0<..<T} - S. \<bar>x' t\<bar> \<le> G * sqrt (1 - (x t)\<^sup>2 - (z t)\<^sup>2) \<and> \<bar>z' t\<bar> \<le> G * sqrt (1 - (x t)\<^sup>2 - (z t)\<^sup>2)"
    and u0: "0 \<le> u" and u1: "u \<le> 1" and hyp: "2 * u \<le> G * T * (1 - u)\<^sup>2 / (2 * sqrt 2)"
  shows "2 * u \<le> G\<^sup>2 * T * integral {0..T} (\<lambda>t. 1 - (x t)\<^sup>2 - (z t)\<^sup>2)"
proof -
  define p where "p = (\<lambda>t. 1 - (x t)\<^sup>2 - (z t)\<^sup>2)"
  define y where "y = (\<lambda>t. sqrt (p t))"
  have Dt: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> x t \<and> 0 \<le> z t \<and> (x t)\<^sup>2 + (z t)\<^sup>2 \<le> 1" using D by blast
  have pnn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> p t"
  proof -
    fix t assume "t \<in> {0..T}"
    from Dt[OF this] have "(x t)\<^sup>2 + (z t)\<^sup>2 \<le> 1" by blast
    thus "0 \<le> p t" unfolding p_def by linarith
  qed
  have p1: "\<And>t. p t \<le> 1" unfolding p_def by (simp add: zero_le_power2)
  have y0: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> y t" unfolding y_def using pnn by simp
  have y2: "\<And>t. t \<in> {0..T} \<Longrightarrow> (y t)\<^sup>2 = p t" unfolding y_def using pnn by simp
  have y1: "\<And>t. y t \<le> 1"
  proof -
    fix t
    have "sqrt (p t) \<le> sqrt 1" by (rule real_sqrt_le_mono[OF p1])
    thus "y t \<le> 1" unfolding y_def by simp
  qed
  have pc: "continuous_on {0..T} p" unfolding p_def by (intro continuous_intros cx cz)
  have yc: "continuous_on {0..T} y" unfolding y_def
    by (rule continuous_on_compose2[OF continuous_on_real_sqrt pc]) (use pnn in auto)
  have bnd': "\<And>t. t \<in> {0<..<T} - S \<Longrightarrow> \<bar>x' t\<bar> \<le> G * y t \<and> \<bar>z' t\<bar> \<le> G * y t"
    using bnd unfolding y_def p_def by simp
  have p0: "p 0 = 0" unfolding p_def using x0 z0 by simp
  have pT: "p T = 0" unfolding p_def using xT zT by simp
  \<comment> \<open>Paso 1: cruce\<close>
  obtain tc where tcr: "0 \<le> tc" "tc \<le> T" and tcxz: "x tc = z tc"
  proof -
    have cg: "continuous_on {0..T} (\<lambda>t. x t - z t)" using cx cz by (intro continuous_intros)
    have conn: "connected ((\<lambda>t. x t - z t) ` {0..T})"
      by (rule connected_continuous_image[OF cg connected_Icc])
    have m1: "(-1::real) \<in> (\<lambda>t. x t - z t) ` {0..T}" using xT zT T by (intro image_eqI[of _ _ T]) auto
    have p1': "(1::real) \<in> (\<lambda>t. x t - z t) ` {0..T}" using x0 z0 T by (intro image_eqI[of _ _ 0]) auto
    have "{-1..1} \<subseteq> (\<lambda>t. x t - z t) ` {0..T}" by (rule connected_contains_Icc[OF conn m1 p1'])
    hence "(0::real) \<in> (\<lambda>t. x t - z t) ` {0..T}" by auto
    then obtain t where "t \<in> {0..T}" "x t - z t = 0" by auto
    thus ?thesis using that by auto
  qed
  define s where "s = z tc"
  have tcD: "tc \<in> {0..T}" using tcr by simp
  have s0: "0 \<le> s" unfolding s_def using Dt[OF tcD] by simp
  have ptc: "p tc = 1 - 2 * s\<^sup>2"
  proof -
    have "p tc = 1 - (z tc)\<^sup>2 - (z tc)\<^sup>2" unfolding p_def tcxz by simp
    thus ?thesis unfolding s_def by simp
  qed
  have xs: "x tc = s" unfolding s_def by (rule tcxz)
  define u0' where "u0' = 2 * s\<^sup>2"
  have hnn: "0 \<le> 1 - u0'" using pnn[OF tcD] ptc unfolding u0'_def by simp
  have u0'0: "0 \<le> u0'" unfolding u0'_def by simp
  \<comment> \<open>Paso 2\<close>
  have Gyc: "continuous_on {0..T} (\<lambda>t. G * y t)" using yc by (intro continuous_intros)
  have Gyi: "\<And>a b. 0 \<le> a \<Longrightarrow> b \<le> T \<Longrightarrow> (\<lambda>t. G * y t) integrable_on {a..b}"
    by (rule integrable_continuous_real, rule continuous_on_subset[OF Gyc]) auto
  have bz: "\<bar>z tc - z 0\<bar> \<le> integral {0..tc} (\<lambda>t. G * y t)"
  proof (rule ftc_bound[where F' = z', OF S tcr(1)])
    show "continuous_on {0..tc} z" by (rule continuous_on_subset[OF cz]) (use tcr in auto)
    show "continuous_on {0..tc} (\<lambda>t. G * y t)" by (rule continuous_on_subset[OF Gyc]) (use tcr in auto)
    show "\<And>t. t \<in> {0..tc} \<Longrightarrow> 0 \<le> G * y t" using G y0 tcr by auto
    fix t assume t: "t \<in> {0<..<tc} - S"
    hence tt: "t \<in> {0<..<T} - S" using tcr by auto
    show "(z has_real_derivative z' t) (at t) \<and> \<bar>z' t\<bar> \<le> G * y t" using der bnd'[OF tt] tt by blast
  qed
  have bx: "\<bar>x T - x tc\<bar> \<le> integral {tc..T} (\<lambda>t. G * y t)"
  proof (rule ftc_bound[where F' = x', OF S tcr(2)])
    show "continuous_on {tc..T} x" by (rule continuous_on_subset[OF cx]) (use tcr in auto)
    show "continuous_on {tc..T} (\<lambda>t. G * y t)" by (rule continuous_on_subset[OF Gyc]) (use tcr in auto)
    show "\<And>t. t \<in> {tc..T} \<Longrightarrow> 0 \<le> G * y t" using G y0 tcr by auto
    fix t assume t: "t \<in> {tc<..<T} - S"
    hence tt: "t \<in> {0<..<T} - S" using tcr by auto
    show "(x has_real_derivative x' t) (at t) \<and> \<bar>x' t\<bar> \<le> G * y t" using der bnd'[OF tt] tt by blast
  qed
  define Iy where "Iy = integral {0..T} y"
  have yi: "(y has_integral Iy) {0..T}" unfolding Iy_def
    using integrable_continuous_real[OF yc] by (rule integrable_integral)
  have Gyh: "((\<lambda>t. G * y t) has_integral G * Iy) {0..T}" using has_integral_mult_right[OF yi, of G] by simp
  have comb: "integral {0..tc} (\<lambda>t. G * y t) + integral {tc..T} (\<lambda>t. G * y t) = G * Iy"
  proof -
    have "integral {0..tc} (\<lambda>t. G * y t) + integral {tc..T} (\<lambda>t. G * y t) = integral {0..T} (\<lambda>t. G * y t)"
      by (rule Henstock_Kurzweil_Integration.integral_combine[OF tcr(1) tcr(2) Gyi[OF order_refl order_refl]])
    thus ?thesis by (rule trans[OF _ integral_unique[OF Gyh]])
  qed
  have s_le1: "s \<le> integral {0..tc} (\<lambda>t. G * y t)" using bz z0 unfolding s_def by (simp add: abs_le_iff)
  have s_le2: "s \<le> integral {tc..T} (\<lambda>t. G * y t)" using bx xT xs by (simp add: abs_le_iff)
  have s2G: "2 * s \<le> G * Iy" using s_le1 s_le2 comb by linarith
  have cs: "Iy\<^sup>2 \<le> T * integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
    unfolding Iy_def by (rule cauchy_schwarz_cont[OF T yc])
  define I where "I = integral {0..T} p"
  have Iyp: "integral {0..T} (\<lambda>t. (y t)\<^sup>2) = I" unfolding I_def by (rule integral_cong) (simp add: y2)
  have goalI: "integral {0..T} (\<lambda>t. 1 - (x t)\<^sup>2 - (z t)\<^sup>2) = I" unfolding I_def p_def ..
  have step2: "2 * u0' \<le> G\<^sup>2 * T * I"
  proof -
    have "(2 * s)\<^sup>2 \<le> (G * Iy)\<^sup>2" by (rule power_mono[OF s2G]) (use s0 in simp)
    also have "... = G\<^sup>2 * Iy\<^sup>2" by (simp add: power_mult_distrib)
    also have "... \<le> G\<^sup>2 * (T * I)" using cs Iyp by (intro mult_left_mono) auto
    finally have "(2 * s)\<^sup>2 \<le> G\<^sup>2 * (T * I)" .
    thus ?thesis unfolding u0'_def by (simp add: power_mult_distrib algebra_simps)
  qed
  \<comment> \<open>Paso 3: Lipschitz\<close>
  define M where "M = 2 * sqrt 2 * G"
  have M0: "0 < M" unfolding M_def using G by simp
  have lip: "\<And>a b. 0 \<le> a \<Longrightarrow> a \<le> b \<Longrightarrow> b \<le> T \<Longrightarrow> \<bar>p b - p a\<bar> \<le> M * (b - a)"
  proof -
    fix a b assume ab: "0 \<le> a" "a \<le> b" "b \<le> T"
    have "\<bar>p b - p a\<bar> \<le> integral {a..b} (\<lambda>t. M)"
    proof (rule ftc_bound[where F' = "\<lambda>t. - (2 * x t * x' t) - 2 * z t * z' t", OF S ab(2)])
      show "continuous_on {a..b} p" by (rule continuous_on_subset[OF pc]) (use ab in auto)
      show "continuous_on {a..b} (\<lambda>t. M)" by (rule continuous_on_const)
      show "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> M" using M0 by simp
      fix t assume t: "t \<in> {a<..<b} - S"
      hence tt: "t \<in> {0<..<T} - S" using ab by auto
      have tD: "t \<in> {0..T}" using tt by auto
      from der tt have hx: "(x has_real_derivative x' t) (at t)" and hz: "(z has_real_derivative z' t) (at t)" by blast+
      have dp: "(p has_real_derivative (- (2 * x t * x' t) - 2 * z t * z' t)) (at t)"
        unfolding p_def using hx hz by (auto intro!: derivative_eq_intros)
      have xt: "0 \<le> x t" and zt: "0 \<le> z t" and xz1: "(x t)\<^sup>2 + (z t)\<^sup>2 \<le> 1" using Dt[OF tD] by auto
      have bd: "\<bar>- (2 * x t * x' t) - 2 * z t * z' t\<bar> \<le> M"
      proof -
        have b1: "\<bar>x' t\<bar> \<le> G * y t" and b2: "\<bar>z' t\<bar> \<le> G * y t" using bnd'[OF tt] by auto
        have a1: "\<bar>- (2 * x t * x' t) - 2 * z t * z' t\<bar> \<le> 2 * x t * \<bar>x' t\<bar> + 2 * z t * \<bar>z' t\<bar>"
          using abs_triangle_ineq4[of "- (2 * x t * x' t)" "2 * z t * z' t"] xt zt by (simp add: abs_mult)
        have a2: "2 * x t * \<bar>x' t\<bar> + 2 * z t * \<bar>z' t\<bar> \<le> 2 * x t * (G * y t) + 2 * z t * (G * y t)"
          using b1 b2 xt zt by (intro add_mono mult_left_mono) auto
        have a3: "2 * x t * (G * y t) + 2 * z t * (G * y t) = 2 * ((x t + z t) * (G * y t))"
          by (simp add: algebra_simps)
        have sxz: "x t + z t \<le> sqrt 2"
        proof (rule real_le_rsqrt)
          have "(x t + z t)\<^sup>2 \<le> 2 * ((x t)\<^sup>2 + (z t)\<^sup>2)"
          proof -
            have e1: "(x t + z t)\<^sup>2 = (x t)\<^sup>2 + (z t)\<^sup>2 + 2 * (x t * z t)" by (simp add: power2_eq_square algebra_simps)
            have e2: "(x t - z t)\<^sup>2 = (x t)\<^sup>2 + (z t)\<^sup>2 - 2 * (x t * z t)" by (simp add: power2_eq_square algebra_simps)
            have e3: "0 \<le> (x t - z t)\<^sup>2" by simp
            have e4: "2 * (x t * z t) \<le> (x t)\<^sup>2 + (z t)\<^sup>2" using e2 e3 by simp
            show ?thesis unfolding e1 using e4 by simp
          qed
          moreover have "2 * ((x t)\<^sup>2 + (z t)\<^sup>2) \<le> 2" using xz1 by simp
          ultimately show "(x t + z t)\<^sup>2 \<le> 2" by (rule order_trans)
        qed
        have gy: "G * y t \<le> G * 1" by (rule mult_left_mono) (use y1 G in auto)
        have a4: "(x t + z t) * (G * y t) \<le> sqrt 2 * (G * 1)"
          by (rule mult_mono[OF sxz gy]) (use G y0[OF tD] xt zt in auto)
        show ?thesis using a1 a2 a3 a4 unfolding M_def by linarith
      qed
      show "(p has_real_derivative - (2 * x t * x' t) - 2 * z t * z' t) (at t) \<and>
            \<bar>- (2 * x t * x' t) - 2 * z t * z' t\<bar> \<le> M" using dp bd by blast
    qed
    moreover have "integral {a..b} (\<lambda>t. M) = M * (b - a)"
    proof (rule integral_unique)
      show "((\<lambda>t. M) has_integral M * (b - a)) {a..b}"
        using has_integral_const_real[of M a b] ab(2) by (simp add: mult.commute)
    qed
    ultimately show "\<bar>p b - p a\<bar> \<le> M * (b - a)" by (rule ord_le_eq_trans)
  qed
  define h where "h = 1 - u0'"
  define w where "w = h / M"
  have w0: "0 \<le> w" unfolding w_def using hnn M0 h_def by simp
  have hMw: "h = M * w" unfolding w_def using M0 by simp
  have ptc_h: "p tc = h" unfolding h_def u0'_def using ptc .
  have wtc: "w \<le> tc"
  proof -
    have "h \<le> M * tc" using lip[OF order_refl tcr(1) tcr(2)] p0 ptc_h hnn h_def by simp
    thus ?thesis unfolding w_def using M0 by (simp add: divide_le_eq mult.commute)
  qed
  have wT: "w \<le> T - tc"
  proof -
    have "h \<le> M * (T - tc)" using lip[OF tcr(1) tcr(2) order_refl] pT ptc_h hnn h_def by simp
    thus ?thesis unfolding w_def using M0 by (simp add: divide_le_eq mult.commute)
  qed
  have lowp: "\<And>t. t \<in> {0..T} \<Longrightarrow> h - M * \<bar>t - tc\<bar> \<le> p t"
  proof -
    fix t assume t: "t \<in> {0..T}"
    show "h - M * \<bar>t - tc\<bar> \<le> p t"
    proof (cases "t \<le> tc")
      case True
      have "\<bar>p tc - p t\<bar> \<le> M * (tc - t)" using lip[of t tc] t True tcr by simp
      thus ?thesis using True ptc_h by (simp add: abs_le_iff abs_of_nonpos)
    next
      case False
      have "\<bar>p t - p tc\<bar> \<le> M * (t - tc)" using lip[of tc t] t False tcr by simp
      thus ?thesis using False ptc_h by (simp add: abs_le_iff abs_of_nonneg)
    qed
  qed
  \<comment> \<open>integral del triangulo\<close>
  have pint: "\<And>a::real. \<And>b::real. 0 \<le> a \<Longrightarrow> b \<le> T \<Longrightarrow> (p has_integral integral {a..b} p) {a..b}"
  proof -
    fix a b :: real assume "0 \<le> a" "b \<le> T"
    have "p integrable_on {a..b}"
      by (rule integrable_continuous_real, rule continuous_on_subset[OF pc]) (use \<open>0 \<le> a\<close> \<open>b \<le> T\<close> in auto)
    thus "(p has_integral integral {a..b} p) {a..b}" by (rule integrable_integral)
  qed
  define a1 where "a1 = tc - w"
  define a3 where "a3 = tc + w"
  have a1r: "0 \<le> a1" "a1 \<le> tc" unfolding a1_def using wtc w0 by auto
  have a3r: "tc \<le> a3" "a3 \<le> T" unfolding a3_def using wT w0 by auto
  have pi0: "p integrable_on {0..T}" using pint[of 0 T] T by (auto simp: has_integral_integrable)
  have pi_sub: "\<And>a::real. \<And>b::real. 0 \<le> a \<Longrightarrow> b \<le> T \<Longrightarrow> p integrable_on {a..b}"
    using pint by (auto simp: has_integral_integrable)
  have nn_int: "\<And>a::real. \<And>b::real. 0 \<le> a \<Longrightarrow> a \<le> b \<Longrightarrow> b \<le> T \<Longrightarrow> 0 \<le> integral {a..b} p"
    by (rule has_integral_nonneg[OF pint]) (use pnn in auto)
  have c1: "integral {0..a1} p + integral {a1..T} p = I" unfolding I_def
    by (rule Henstock_Kurzweil_Integration.integral_combine[OF a1r(1) _ pi0]) (use a1r a3r tcr in linarith)
  have c2: "integral {a1..a3} p + integral {a3..T} p = integral {a1..T} p"
    by (rule Henstock_Kurzweil_Integration.integral_combine[OF _ a3r(2) pi_sub[OF a1r(1) order_refl]]) (use a1r a3r in linarith)
  have c3: "integral {a1..tc} p + integral {tc..a3} p = integral {a1..a3} p"
    by (rule Henstock_Kurzweil_Integration.integral_combine[OF a1r(2) a3r(1) pi_sub[OF a1r(1) a3r(2)]])
  have L: "h * w / 2 \<le> integral {a1..tc} p"
  proof -
    have tl: "((\<lambda>t. h - M * (tc - t)) has_integral h * w / 2) {a1..tc}" unfolding a1_def by (rule tri_left[OF M0 w0 hMw])
    have ineq: "\<And>t. t \<in> {a1..tc} \<Longrightarrow> h - M * (tc - t) \<le> p t"
    proof -
      fix t assume t: "t \<in> {a1..tc}"
      hence tD: "t \<in> {0..T}" using a1r tcr by auto
      have "\<bar>t - tc\<bar> = tc - t" using t by (simp add: abs_of_nonpos)
      thus "h - M * (tc - t) \<le> p t" using lowp[OF tD] by simp
    qed
    show ?thesis by (rule has_integral_le[OF tl pint[OF a1r(1) tcr(2)] ineq])
  qed
  have R: "h * w / 2 \<le> integral {tc..a3} p"
  proof -
    have tr: "((\<lambda>t. h - M * (t - tc)) has_integral h * w / 2) {tc..a3}" unfolding a3_def by (rule tri_right[OF M0 w0 hMw])
    have ineq: "\<And>t. t \<in> {tc..a3} \<Longrightarrow> h - M * (t - tc) \<le> p t"
    proof -
      fix t assume t: "t \<in> {tc..a3}"
      hence tD: "t \<in> {0..T}" using a3r tcr by auto
      have "\<bar>t - tc\<bar> = t - tc" using t by (simp add: abs_of_nonneg)
      thus "h - M * (t - tc) \<le> p t" using lowp[OF tD] by simp
    qed
    show ?thesis by (rule has_integral_le[OF tr pint[OF tcr(1) a3r(2)] ineq])
  qed
  have n1: "0 \<le> integral {0..a1} p" by (rule nn_int[OF order_refl]) (use a1r a3r tcr in linarith)+
  have n2: "0 \<le> integral {a3..T} p" by (rule nn_int[OF _ a3r(2) order_refl]) (use a1r a3r tcr in linarith)
  have Ilow: "h * w \<le> I" using c1 c2 c3 L R n1 n2 by linarith
  have hwM: "h * w = h\<^sup>2 / M" unfolding w_def by (simp add: power2_eq_square)
  \<comment> \<open>Paso 4\<close>
  show ?thesis unfolding goalI
  proof (cases "u \<le> u0'")
    case True
    have "2 * u \<le> 2 * u0'" using True by simp
    also have "... \<le> G\<^sup>2 * T * I" by (rule step2)
    finally show "2 * u \<le> G\<^sup>2 * T * I" .
  next
    case False
    hence lt: "u0' < u" by simp
    have hge: "1 - u \<le> h" unfolding h_def using lt by simp
    have h2: "(1 - u)\<^sup>2 \<le> h\<^sup>2" by (rule power_mono[OF hge]) (use u1 in simp)
    have GM: "G\<^sup>2 * T * (h\<^sup>2 / M) = G * T * h\<^sup>2 / (2 * sqrt 2)"
      unfolding M_def using G by (simp add: field_simps power2_eq_square)
    have "2 * u \<le> G * T * (1 - u)\<^sup>2 / (2 * sqrt 2)" by (rule hyp)
    also have "... \<le> G * T * h\<^sup>2 / (2 * sqrt 2)"
      using h2 G T by (intro divide_right_mono mult_left_mono) auto
    also have "... = G\<^sup>2 * T * (h\<^sup>2 / M)" by (rule GM[symmetric])
    also have "... = G\<^sup>2 * T * (h * w)" unfolding hwM ..
    also have "... \<le> G\<^sup>2 * T * I" using Ilow G T by (intro mult_left_mono) auto
    finally show "2 * u \<le> G\<^sup>2 * T * I" .
  qed
qed

end
