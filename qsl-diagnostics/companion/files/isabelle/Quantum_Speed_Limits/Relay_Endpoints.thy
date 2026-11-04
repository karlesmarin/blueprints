(*  Title:      Relay_Endpoints.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Occupation of the end qubits of a relay: G times the integrated occupation of emitter and receiver is at least
    Phi(x(0)) - Phi(x(T)) + Phi(z(T)) - Phi(z(0)), hence pi/2 for a complete transfer, for absolutely
    continuous amplitudes with a negligible exceptional set.
*)
theory Relay_Endpoints
  imports "HOL-Analysis.Analysis"
begin

text \<open>Endpoint occupation of a relay: if the amplitude w of an endpoint mode satisfies the Lipschitz bound with the bus amplitude y, then Phi(w) moves at most by G times the integrated occupation of w.\<close>

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

definition Phi :: "real \<Rightarrow> real" where
  "Phi u = (arcsin u - u * sqrt (1 - u\<^sup>2)) / 2"

lemma Phi_values: "Phi 0 = 0" "Phi 1 = pi / 4"
  unfolding Phi_def by (simp_all add: arcsin_1)

lemma Phi_cont: "continuous_on {0..1} Phi"
proof -
  have "continuous_on {-1..1} arcsin" by (rule continuous_on_arcsin')
  hence a: "continuous_on {0..1} arcsin" by (rule continuous_on_subset) auto
  show ?thesis unfolding Phi_def
    by (intro continuous_intros a continuous_on_compose2[OF continuous_on_real_sqrt]) auto
qed

lemma Phi_deriv:
  fixes v :: real assumes v: "-1 < v" "v < 1"
  shows "(Phi has_real_derivative v\<^sup>2 / sqrt (1 - v\<^sup>2)) (at v)"
proof -
  have p: "0 < 1 - v\<^sup>2"
  proof -
    have "(v - 1) * (v + 1) < 0" by (rule mult_neg_pos) (use v in auto)
    moreover have "v\<^sup>2 - 1 = (v - 1) * (v + 1)" by (simp add: power2_eq_square algebra_simps)
    ultimately show ?thesis by linarith
  qed
  define s where "s = sqrt (1 - v\<^sup>2)"
  have s0: "0 < s" unfolding s_def using p by simp
  have s2: "s\<^sup>2 = 1 - v\<^sup>2" unfolding s_def using p by simp
  have d1: "(arcsin has_real_derivative inverse s) (at v)"
    using DERIV_arcsin[OF v] unfolding s_def by (simp add: inverse_eq_divide)
  have d0: "(sqrt has_real_derivative inverse s / 2) (at (1 - v\<^sup>2))"
    using DERIV_real_sqrt[OF p] unfolding s_def .
  have d2: "((\<lambda>u::real. 1 - u\<^sup>2) has_real_derivative - (2 * v)) (at v)"
    by (auto intro!: derivative_eq_intros)
  have d3: "((\<lambda>u. sqrt (1 - u\<^sup>2)) has_real_derivative inverse s / 2 * (- (2 * v))) (at v)"
    using DERIV_chain2[OF d0 d2] by simp
  have d4: "((\<lambda>u. (arcsin u - u * sqrt (1 - u\<^sup>2)) / 2) has_real_derivative
      (inverse s - (1 * sqrt (1 - v\<^sup>2) + v * (inverse s / 2 * (- (2 * v))))) / 2) (at v)"
  proof -
    have dm: "((\<lambda>u. u * sqrt (1 - u\<^sup>2)) has_real_derivative
        (1 * sqrt (1 - v\<^sup>2) + v * (inverse s / 2 * (- (2 * v))))) (at v)"
      using DERIV_mult[OF DERIV_ident d3] by (simp add: algebra_simps)
    have dd: "((\<lambda>u. arcsin u - u * sqrt (1 - u\<^sup>2)) has_real_derivative
        (inverse s - (1 * sqrt (1 - v\<^sup>2) + v * (inverse s / 2 * (- (2 * v)))))) (at v)"
      by (rule DERIV_diff[OF d1 dm])
    show ?thesis by (rule DERIV_cdivide[OF dd])
  qed
  have "(inverse s - (1 * sqrt (1 - v\<^sup>2) + v * (inverse s / 2 * (- (2 * v))))) / 2 = v\<^sup>2 / s"
  proof -
    have "(inverse s - (1 * sqrt (1 - v\<^sup>2) + v * (inverse s / 2 * (- (2 * v))))) / 2 = (1 - s\<^sup>2 + v\<^sup>2) / (2 * s)"
      unfolding s_def[symmetric] using s0 by (simp add: field_simps power2_eq_square)
    also have "... = v\<^sup>2 / s"
    proof -
      have e: "1 - s\<^sup>2 + v\<^sup>2 = 2 * v\<^sup>2" using s2 by simp
      show ?thesis using s0 by (simp add: e)
    qed
    finally show ?thesis .
  qed
  thus ?thesis using d4 unfolding Phi_def s_def by simp
qed


lemma ftc_bound_ac:
  fixes F F' g :: "real \<Rightarrow> real" and a b :: real and S :: "real set"
  assumes S: "negligible S" and ab: "a \<le> b"
    and Fac: "absolutely_continuous_on {a..b} F" and gc: "continuous_on {a..b} g"
    and g0: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> g t"
    and der: "\<And>t. t \<in> {a<..<b} - S \<Longrightarrow> (F has_real_derivative F' t) (at t) \<and> \<bar>F' t\<bar> \<le> g t"
  shows "\<bar>F b - F a\<bar> \<le> integral {a..b} g"
proof -
  define f where "f = (\<lambda>t. if t \<in> {a<..<b} - S then F' t else 0)"
  define S' where "S' = {a, b} \<union> S"
  have S'n: "negligible S'" unfolding S'_def by (rule negligible_Un[OF negligible_finite[of "{a, b}"] S]) simp
  have fd: "\<And>t. t \<in> {a..b} - S' \<Longrightarrow> (F has_vector_derivative f t) (at t within {a..b})"
  proof -
    fix t assume t: "t \<in> {a..b} - S'"
    hence t2: "t \<in> {a<..<b} - S" unfolding S'_def by auto
    have "f t = F' t" unfolding f_def using t2 by simp
    hence "(F has_vector_derivative f t) (at t)"
      using der[OF t2] by (simp add: has_real_derivative_iff_has_vector_derivative)
    thus "(F has_vector_derivative f t) (at t within {a..b})" by (rule has_vector_derivative_at_within)
  qed
  have ftc: "(f has_integral F b - F a) {a..b}"
    by (rule fundamental_theorem_of_calculus_absolutely_continuous[OF S'n ab Fac fd])
  define I where "I = integral {a..b} g"
  have gi: "(g has_integral I) {a..b}" unfolding I_def
    using integrable_continuous_real[OF gc] by (rule integrable_integral)
  have fle: "\<And>t. t \<in> {a..b} \<Longrightarrow> f t \<le> g t \<and> - f t \<le> g t"
  proof -
    fix t assume t: "t \<in> {a..b}"
    show "f t \<le> g t \<and> - f t \<le> g t"
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
  have up: "F b - F a \<le> I" by (rule has_integral_le[OF ftc gi]) (use fle in auto)
  have fneg: "((\<lambda>t. - f t) has_integral - (F b - F a)) {a..b}" by (rule has_integral_neg[OF ftc])
  have lo: "- (F b - F a) \<le> I" by (rule has_integral_le[OF fneg gi]) (use fle in auto)
  show ?thesis unfolding I_def[symmetric] using up lo by (simp add: abs_le_iff)
qed

lemma Phi_lip:
  fixes c :: real assumes c0: "0 \<le> c" and c1: "c < 1"
  shows "\<And>p q. p \<in> {0..c} \<Longrightarrow> q \<in> {0..c} \<Longrightarrow> \<bar>Phi p - Phi q\<bar> \<le> 1 / sqrt (1 - c\<^sup>2) * \<bar>p - q\<bar>"
proof -
  have cc: "c\<^sup>2 < 1" 
  proof -
    have "c * c \<le> c * 1" by (rule mult_left_mono) (use c0 c1 in auto)
    thus ?thesis using c1 by (simp add: power2_eq_square)
  qed
  have sc: "0 < sqrt (1 - c\<^sup>2)" using cc by simp
  have key: "\<And>p q. 0 \<le> p \<Longrightarrow> p < q \<Longrightarrow> q \<le> c \<Longrightarrow> \<bar>Phi q - Phi p\<bar> \<le> 1 / sqrt (1 - c\<^sup>2) * (q - p)"
  proof -
    fix p q :: real assume p: "0 \<le> p" and pq: "p < q" and q: "q \<le> c"
    have "\<exists>\<xi>. p < \<xi> \<and> \<xi> < q \<and> Phi q - Phi p = (q - p) * (\<xi>\<^sup>2 / sqrt (1 - \<xi>\<^sup>2))"
    proof (rule MVT2[OF pq])
      fix x assume x: "p \<le> x" "x \<le> q"
      show "DERIV Phi x :> x\<^sup>2 / sqrt (1 - x\<^sup>2)" by (rule Phi_deriv) (use x p q c1 in auto)
    qed
    then obtain \<xi> where xi: "p < \<xi>" "\<xi> < q" and eq: "Phi q - Phi p = (q - p) * (\<xi>\<^sup>2 / sqrt (1 - \<xi>\<^sup>2))" by blast
    have x0: "0 \<le> \<xi>" using xi p by simp
    have xc: "\<xi> \<le> c" using xi q by simp
    have x2: "\<xi>\<^sup>2 \<le> c\<^sup>2" using x0 xc by (simp add: power_mono)
    have sx: "sqrt (1 - c\<^sup>2) \<le> sqrt (1 - \<xi>\<^sup>2)" using x2 by simp
    have sx0: "0 < sqrt (1 - \<xi>\<^sup>2)" using x2 cc by simp
    have xs: "\<xi>\<^sup>2 \<le> 1" using x2 cc by simp
    have "\<xi>\<^sup>2 / sqrt (1 - \<xi>\<^sup>2) \<le> 1 / sqrt (1 - c\<^sup>2)"
      by (rule frac_le) (use xs sx sc in auto)
    moreover have r0: "0 \<le> \<xi>\<^sup>2 / sqrt (1 - \<xi>\<^sup>2)" using sx0 by simp
    ultimately have a2: "(q - p) * (\<xi>\<^sup>2 / sqrt (1 - \<xi>\<^sup>2)) \<le> (q - p) * (1 / sqrt (1 - c\<^sup>2))"
      by (intro mult_left_mono) (use pq in auto)
    have a1: "0 \<le> (q - p) * (\<xi>\<^sup>2 / sqrt (1 - \<xi>\<^sup>2))" by (rule mult_nonneg_nonneg) (use pq r0 in auto)
    show "\<bar>Phi q - Phi p\<bar> \<le> 1 / sqrt (1 - c\<^sup>2) * (q - p)"
      unfolding eq by (subst abs_of_nonneg[OF a1]) (use a2 in \<open>simp add: mult.commute\<close>)
  qed
  fix p q :: real assume p: "p \<in> {0..c}" and q: "q \<in> {0..c}"
  show "\<bar>Phi p - Phi q\<bar> \<le> 1 / sqrt (1 - c\<^sup>2) * \<bar>p - q\<bar>"
  proof (cases p q rule: linorder_cases)
    case less
    from key[of p q] less p q show ?thesis by (simp add: abs_minus_commute)
  next
    case equal thus ?thesis by simp
  next
    case greater
    from key[of q p] greater p q show ?thesis by simp
  qed
qed

lemma Phi_lip_nonneg:
  fixes c :: real assumes c0: "0 \<le> c" and c1: "c < 1"
  shows "0 \<le> 1 / sqrt (1 - c\<^sup>2)" 
proof -
  have "c * c \<le> c * 1" by (rule mult_left_mono) (use c0 c1 in auto)
  hence "c\<^sup>2 < 1" using c1 by (simp add: power2_eq_square)
  hence "0 < sqrt (1 - c\<^sup>2)" by simp
  thus ?thesis by simp
qed

lemma endpoint_window:
  fixes w y w' :: "real \<Rightarrow> real" and G T :: real and S :: "real set"
  assumes T: "0 < T" and G: "0 < G" and S: "countable S"
    and wc: "continuous_on {0..T} w" and yc: "continuous_on {0..T} y"
    and nrm: "\<forall>t\<in>{0..T}. 0 \<le> w t \<and> 0 \<le> y t \<and> (w t)\<^sup>2 + (y t)\<^sup>2 \<le> 1"
    and der: "\<forall>t\<in>{0<..<T} - S. (w has_real_derivative w' t) (at t) \<and> \<bar>w' t\<bar> \<le> G * y t"
  shows "\<bar>Phi (w T) - Phi (w 0)\<bar> \<le> G * integral {0..T} (\<lambda>t. (w t)\<^sup>2)"
proof -
  have w1: "\<And>t. t \<in> {0..T} \<Longrightarrow> w t \<le> 1"
  proof -
    fix t assume t: "t \<in> {0..T}"
    from nrm t have a: "0 \<le> w t" and b: "(w t)\<^sup>2 + (y t)\<^sup>2 \<le> 1" by auto
    have y2: "0 \<le> (y t)\<^sup>2" by simp
    have h1: "(w t)\<^sup>2 \<le> 1" using b y2 by linarith
    have "(w t)\<^sup>2 \<le> 1\<^sup>2" using h1 by simp
    thus "w t \<le> 1" by (rule power2_le_imp_le) simp
  qed
  have gc: "continuous_on {0..T} (\<lambda>t. G * (w t)\<^sup>2)" using wc by (intro continuous_intros)
  have bound: "\<And>c. 0 \<le> c \<Longrightarrow> c < 1 \<Longrightarrow>
      \<bar>Phi (c * w T) - Phi (c * w 0)\<bar> \<le> G * integral {0..T} (\<lambda>t. (w t)\<^sup>2)"
  proof -
    fix c :: real assume c0: "0 \<le> c" and c1: "c < 1"
    define F where "F = (\<lambda>t. Phi (c * w t))"
    define F' where "F' = (\<lambda>t. (c * w t)\<^sup>2 / sqrt (1 - (c * w t)\<^sup>2) * (c * w' t))"
    have cw01: "\<And>t. t \<in> {0..T} \<Longrightarrow> c * w t \<in> {0..1}"
    proof -
      fix t assume t: "t \<in> {0..T}"
      have "0 \<le> c * w t" using c0 nrm t by simp
      moreover have "c * w t \<le> 1" using c1 w1[OF t] nrm t c0 by (simp add: mult_le_one)
      ultimately show "c * w t \<in> {0..1}" by simp
    qed
    have Fc: "continuous_on {0..T} F" unfolding F_def
      by (rule continuous_on_compose2[OF Phi_cont]) (use wc cw01 in \<open>auto intro!: continuous_intros\<close>)
    have "\<bar>F T - F 0\<bar> \<le> integral {0..T} (\<lambda>t. G * (w t)\<^sup>2)"
    proof (rule ftc_bound[where F' = F', OF S less_imp_le[OF T] Fc gc])
      fix t assume t: "t \<in> {0..T}"
      show "0 \<le> G * (w t)\<^sup>2" using G by simp
    next
      fix t assume t: "t \<in> {0<..<T} - S"
      hence tt: "t \<in> {0..T}" by auto
      from der t have hw: "(w has_real_derivative w' t) (at t)" and wb: "\<bar>w' t\<bar> \<le> G * y t" by auto
      from nrm tt have w0: "0 \<le> w t" and y0: "0 \<le> y t" and n: "(w t)\<^sup>2 + (y t)\<^sup>2 \<le> 1" by auto
      have cw2: "(c * w t)\<^sup>2 \<le> (w t)\<^sup>2"
      proof -
        have "c * w t \<le> 1 * w t" by (rule mult_right_mono) (use c1 w0 in auto)
        hence "c * w t \<le> w t" by simp
        thus ?thesis using c0 w0 by (simp add: power2_eq_square mult_mono')
      qed
      have cwb: "c * w t \<in> {0..1}" by (rule cw01[OF tt])
      have cw1: "c * w t < 1"
      proof -
        have "c * w t \<le> c * 1" by (rule mult_left_mono) (use w1[OF tt] c0 in auto)
        thus ?thesis using c1 by simp
      qed
      have cw0: "-1 < c * w t" using cwb by simp
      have dP: "(Phi has_real_derivative (c * w t)\<^sup>2 / sqrt (1 - (c * w t)\<^sup>2)) (at (c * w t))"
        by (rule Phi_deriv[OF cw0 cw1])
      have dc: "((\<lambda>t. c * w t) has_real_derivative c * w' t) (at t)" using hw by (auto intro!: derivative_eq_intros)
      have dF: "(F has_real_derivative F' t) (at t)" unfolding F_def F'_def
        using DERIV_chain2[OF dP dc] by simp
      define s where "s = sqrt (1 - (c * w t)\<^sup>2)"
      have cwsq: "(c * w t)\<^sup>2 < 1"
      proof -
        have "(c * w t)\<^sup>2 < 1\<^sup>2" by (rule power_strict_mono) (use cwb cw1 in auto)
        thus ?thesis by simp
      qed
      have s0: "0 < s" unfolding s_def using cwsq by simp
      have ys: "y t \<le> s"
      proof -
        have s2: "s\<^sup>2 = 1 - (c * w t)\<^sup>2" unfolding s_def using cwsq by simp
        have "(y t)\<^sup>2 \<le> s\<^sup>2" using n cw2 s2 by linarith
        thus ?thesis by (rule power2_le_imp_le) (use s0 in simp)
      qed
      have "\<bar>F' t\<bar> = (c * w t)\<^sup>2 / s * (c * \<bar>w' t\<bar>)" unfolding F'_def s_def[symmetric]
        using s0 c0 by (simp add: abs_mult)
      also have "... \<le> (w t)\<^sup>2 / s * (c * (G * y t))"
      proof (rule mult_mono)
        show "(c * w t)\<^sup>2 / s \<le> (w t)\<^sup>2 / s" using cw2 s0 by (simp add: divide_right_mono)
        show "c * \<bar>w' t\<bar> \<le> c * (G * y t)" using wb c0 by (rule mult_left_mono)
        show "0 \<le> (w t)\<^sup>2 / s" using s0 by simp
        show "0 \<le> c * \<bar>w' t\<bar>" using c0 by simp
      qed
      also have "... \<le> (w t)\<^sup>2 / s * (1 * (G * s))"
      proof (rule mult_left_mono)
        show "c * (G * y t) \<le> 1 * (G * s)" using c1 ys G y0 by (intro mult_mono) auto
        show "0 \<le> (w t)\<^sup>2 / s" using s0 by simp
      qed
      also have "... = G * (w t)\<^sup>2" using s0 by (simp add: field_simps)
      finally show "(F has_real_derivative F' t) (at t) \<and> \<bar>F' t\<bar> \<le> G * (w t)\<^sup>2" using dF by simp
    qed
    thus "\<bar>Phi (c * w T) - Phi (c * w 0)\<bar> \<le> G * integral {0..T} (\<lambda>t. (w t)\<^sup>2)"
      unfolding F_def using integral_cmul by simp
  qed
  define cn where "cn = (\<lambda>n::nat. 1 - 1 / (real n + 2))"
  have cn_t: "cn \<longlonglongrightarrow> 1" unfolding cn_def
  proof -
    have "(\<lambda>n::nat. 1 / (real n + 2)) \<longlonglongrightarrow> 0"
      by (rule real_tendsto_divide_at_top[OF tendsto_const])
         (subst add.commute, rule filterlim_tendsto_add_at_top[OF tendsto_const filterlim_real_sequentially])
    from tendsto_diff[OF tendsto_const this] show "(\<lambda>n. 1 - 1 / (real n + 2)) \<longlonglongrightarrow> 1" by simp
  qed
  have cn01: "\<And>n. 0 \<le> cn n \<and> cn n < 1" unfolding cn_def by (auto simp: field_simps)
  have lim: "\<And>a. 0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> (\<lambda>n. Phi (cn n * a)) \<longlonglongrightarrow> Phi a"
  proof -
    fix a :: real assume a0: "0 \<le> a" and a1: "a \<le> 1"
    have "(\<lambda>n. cn n * a) \<longlonglongrightarrow> 1 * a" by (intro tendsto_intros cn_t)
    hence t1: "(\<lambda>n. cn n * a) \<longlonglongrightarrow> a" by simp
    have ev: "\<forall>\<^sub>F n in sequentially. cn n * a \<in> {0..1}"
    proof (rule eventuallyI)
      fix n
      have "cn n * a \<le> 1 * 1" by (rule mult_mono) (use cn01[of n] a0 a1 in auto)
      moreover have "0 \<le> cn n * a" using cn01[of n] a0 by simp
      ultimately show "cn n * a \<in> {0..1}" by simp
    qed
    have al: "a \<in> {0..1}" using a0 a1 by simp
    from continuous_on_tendsto_compose[OF Phi_cont t1 al ev] show "(\<lambda>n. Phi (cn n * a)) \<longlonglongrightarrow> Phi a" by simp
  qed
  have wT: "0 \<le> w T" "w T \<le> 1" and w00: "0 \<le> w 0" "w 0 \<le> 1" using nrm w1 T by auto
  have "(\<lambda>n. \<bar>Phi (cn n * w T) - Phi (cn n * w 0)\<bar>) \<longlonglongrightarrow> \<bar>Phi (w T) - Phi (w 0)\<bar>"
    by (intro tendsto_intros lim wT w00)
  thus ?thesis by (rule LIMSEQ_le_const2) (use bound cn01 in auto)
qed

theorem endpoint_occupation:
  fixes x z y x' z' :: "real \<Rightarrow> real" and G T :: real and S :: "real set"
  assumes T: "0 < T" and G: "0 < G" and S: "countable S"
    and xc: "continuous_on {0..T} x" and zc: "continuous_on {0..T} z" and yc: "continuous_on {0..T} y"
    and nrm: "\<forall>t\<in>{0..T}. 0 \<le> x t \<and> 0 \<le> z t \<and> 0 \<le> y t \<and> (x t)\<^sup>2 + (y t)\<^sup>2 + (z t)\<^sup>2 \<le> 1"
    and bd: "x 0 = 1" "x T = 0" "z 0 = 0" "z T = 1"
    and der: "\<forall>t\<in>{0<..<T} - S. (x has_real_derivative x' t) (at t) \<and> (z has_real_derivative z' t) (at t)
      \<and> \<bar>x' t\<bar> \<le> G * y t \<and> \<bar>z' t\<bar> \<le> G * y t"
  shows "pi / 2 \<le> G * integral {0..T} (\<lambda>t. (x t)\<^sup>2 + (z t)\<^sup>2)"
proof -
  have nx: "\<forall>t\<in>{0..T}. 0 \<le> x t \<and> 0 \<le> y t \<and> (x t)\<^sup>2 + (y t)\<^sup>2 \<le> 1"
  proof
    fix t assume t: "t \<in> {0..T}"
    from nrm t have "0 \<le> x t" "0 \<le> y t" "(x t)\<^sup>2 + (y t)\<^sup>2 + (z t)\<^sup>2 \<le> 1" by auto
    moreover have "0 \<le> (z t)\<^sup>2" by simp
    ultimately show "0 \<le> x t \<and> 0 \<le> y t \<and> (x t)\<^sup>2 + (y t)\<^sup>2 \<le> 1" by linarith
  qed
  have nz: "\<forall>t\<in>{0..T}. 0 \<le> z t \<and> 0 \<le> y t \<and> (z t)\<^sup>2 + (y t)\<^sup>2 \<le> 1"
  proof
    fix t assume t: "t \<in> {0..T}"
    from nrm t have "0 \<le> z t" "0 \<le> y t" "(x t)\<^sup>2 + (y t)\<^sup>2 + (z t)\<^sup>2 \<le> 1" by auto
    moreover have "0 \<le> (x t)\<^sup>2" by simp
    ultimately show "0 \<le> z t \<and> 0 \<le> y t \<and> (z t)\<^sup>2 + (y t)\<^sup>2 \<le> 1" by linarith
  qed
  have ex: "\<bar>Phi (x T) - Phi (x 0)\<bar> \<le> G * integral {0..T} (\<lambda>t. (x t)\<^sup>2)"
    by (rule endpoint_window[OF T G S xc yc nx]) (use der in auto)
  have ez: "\<bar>Phi (z T) - Phi (z 0)\<bar> \<le> G * integral {0..T} (\<lambda>t. (z t)\<^sup>2)"
    by (rule endpoint_window[OF T G S zc yc nz]) (use der in auto)
  have x2: "(\<lambda>t. (x t)\<^sup>2) integrable_on {0..T}" using xc by (intro integrable_continuous_real continuous_intros)
  have z2: "(\<lambda>t. (z t)\<^sup>2) integrable_on {0..T}" using zc by (intro integrable_continuous_real continuous_intros)
  have "integral {0..T} (\<lambda>t. (x t)\<^sup>2 + (z t)\<^sup>2) = integral {0..T} (\<lambda>t. (x t)\<^sup>2) + integral {0..T} (\<lambda>t. (z t)\<^sup>2)"
    by (rule integral_add[OF x2 z2])
  moreover have "\<bar>Phi (x T) - Phi (x 0)\<bar> = pi / 4"
  proof -
    have "Phi (x T) - Phi (x 0) = - (pi / 4)" using bd Phi_values by simp
    thus ?thesis by simp
  qed
  moreover have "\<bar>Phi (z T) - Phi (z 0)\<bar> = pi / 4"
  proof -
    have h: "Phi (z T) - Phi (z 0) = pi / 4" using bd Phi_values by simp
    show ?thesis unfolding h using pi_gt_zero by simp
  qed
  ultimately show ?thesis using ex ez by (simp add: algebra_simps)
qed


lemma endpoint_window_ac:
  fixes w y w' :: "real \<Rightarrow> real" and G T :: real and S :: "real set"
  assumes T: "0 < T" and G: "0 < G" and S: "negligible S"
    and wac: "absolutely_continuous_on {0..T} w" and yc: "continuous_on {0..T} y"
    and nrm: "\<forall>t\<in>{0..T}. 0 \<le> w t \<and> 0 \<le> y t \<and> (w t)\<^sup>2 + (y t)\<^sup>2 \<le> 1"
    and der: "\<forall>t\<in>{0<..<T} - S. (w has_real_derivative w' t) (at t) \<and> \<bar>w' t\<bar> \<le> G * y t"
  shows "\<bar>Phi (w T) - Phi (w 0)\<bar> \<le> G * integral {0..T} (\<lambda>t. (w t)\<^sup>2)"
proof -
  have wc: "continuous_on {0..T} w"
    by (rule absolutely_continuous_on_imp_continuous[OF wac]) simp
  have w1: "\<And>t. t \<in> {0..T} \<Longrightarrow> w t \<le> 1"
  proof -
    fix t assume t: "t \<in> {0..T}"
    from nrm t have a: "0 \<le> w t" and b: "(w t)\<^sup>2 + (y t)\<^sup>2 \<le> 1" by auto
    have y2: "0 \<le> (y t)\<^sup>2" by simp
    have h1: "(w t)\<^sup>2 \<le> 1" using b y2 by linarith
    have "(w t)\<^sup>2 \<le> 1\<^sup>2" using h1 by simp
    thus "w t \<le> 1" by (rule power2_le_imp_le) simp
  qed
  have gc: "continuous_on {0..T} (\<lambda>t. G * (w t)\<^sup>2)" using wc by (intro continuous_intros)
  have bound: "\<And>c. 0 \<le> c \<Longrightarrow> c < 1 \<Longrightarrow>
      \<bar>Phi (c * w T) - Phi (c * w 0)\<bar> \<le> G * integral {0..T} (\<lambda>t. (w t)\<^sup>2)"
  proof -
    fix c :: real assume c0: "0 \<le> c" and c1: "c < 1"
    define F where "F = (\<lambda>t. Phi (c * w t))"
    define F' where "F' = (\<lambda>t. (c * w t)\<^sup>2 / sqrt (1 - (c * w t)\<^sup>2) * (c * w' t))"
    have cw01: "\<And>t. t \<in> {0..T} \<Longrightarrow> c * w t \<in> {0..1}"
    proof -
      fix t assume t: "t \<in> {0..T}"
      have "0 \<le> c * w t" using c0 nrm t by simp
      moreover have "c * w t \<le> 1" using c1 w1[OF t] nrm t c0 by (simp add: mult_le_one)
      ultimately show "c * w t \<in> {0..1}" by simp
    qed
    have cw0c: "\<And>t. t \<in> {0..T} \<Longrightarrow> c * w t \<in> {0..c}"
    proof -
      fix t assume t: "t \<in> {0..T}"
      have "0 \<le> c * w t" using c0 nrm t by simp
      moreover have "c * w t \<le> c * 1" by (rule mult_left_mono) (use c0 w1[OF t] in auto)
      ultimately show "c * w t \<in> {0..c}" by simp
    qed
    have cwac: "absolutely_continuous_on {0..T} (\<lambda>t. c * w t)"
      using absolutely_continuous_on_cmul[OF wac, of c] by (simp add: real_scaleR_def)
    have Fac: "absolutely_continuous_on {0..T} F" unfolding F_def
    proof -
      have "absolutely_continuous_on {0..T} (Phi \<circ> (\<lambda>t. c * w t))"
      proof (rule absolutely_continuous_on_Lipschitz_compose[OF cwac _ Phi_lip_nonneg[OF c0 c1]])
        fix p q assume "p \<in> (\<lambda>t. c * w t) ` {0..T}" "q \<in> (\<lambda>t. c * w t) ` {0..T}"
        hence "p \<in> {0..c}" "q \<in> {0..c}" using cw0c by auto
        thus "norm (Phi p - Phi q) \<le> 1 / sqrt (1 - c\<^sup>2) * \<bar>p - q\<bar>" using Phi_lip[OF c0 c1] by simp
      qed
      thus "absolutely_continuous_on {0..T} (\<lambda>t. Phi (c * w t))" by (simp add: o_def)
    qed
    have "\<bar>F T - F 0\<bar> \<le> integral {0..T} (\<lambda>t. G * (w t)\<^sup>2)"
    proof (rule ftc_bound_ac[where F' = F', OF S less_imp_le[OF T] Fac gc])
      fix t assume t: "t \<in> {0..T}"
      show "0 \<le> G * (w t)\<^sup>2" using G by simp
    next
      fix t assume t: "t \<in> {0<..<T} - S"
      hence tt: "t \<in> {0..T}" by auto
      from der t have hw: "(w has_real_derivative w' t) (at t)" and wb: "\<bar>w' t\<bar> \<le> G * y t" by auto
      from nrm tt have w0: "0 \<le> w t" and y0: "0 \<le> y t" and n: "(w t)\<^sup>2 + (y t)\<^sup>2 \<le> 1" by auto
      have cw2: "(c * w t)\<^sup>2 \<le> (w t)\<^sup>2"
      proof -
        have "c * w t \<le> 1 * w t" by (rule mult_right_mono) (use c1 w0 in auto)
        hence "c * w t \<le> w t" by simp
        thus ?thesis using c0 w0 by (simp add: power2_eq_square mult_mono')
      qed
      have cwb: "c * w t \<in> {0..1}" by (rule cw01[OF tt])
      have cw1: "c * w t < 1"
      proof -
        have "c * w t \<le> c * 1" by (rule mult_left_mono) (use w1[OF tt] c0 in auto)
        thus ?thesis using c1 by simp
      qed
      have cw0: "-1 < c * w t" using cwb by simp
      have dP: "(Phi has_real_derivative (c * w t)\<^sup>2 / sqrt (1 - (c * w t)\<^sup>2)) (at (c * w t))"
        by (rule Phi_deriv[OF cw0 cw1])
      have dc: "((\<lambda>t. c * w t) has_real_derivative c * w' t) (at t)" using hw by (auto intro!: derivative_eq_intros)
      have dF: "(F has_real_derivative F' t) (at t)" unfolding F_def F'_def
        using DERIV_chain2[OF dP dc] by simp
      define s where "s = sqrt (1 - (c * w t)\<^sup>2)"
      have cwsq: "(c * w t)\<^sup>2 < 1"
      proof -
        have "(c * w t)\<^sup>2 < 1\<^sup>2" by (rule power_strict_mono) (use cwb cw1 in auto)
        thus ?thesis by simp
      qed
      have s0: "0 < s" unfolding s_def using cwsq by simp
      have ys: "y t \<le> s"
      proof -
        have s2: "s\<^sup>2 = 1 - (c * w t)\<^sup>2" unfolding s_def using cwsq by simp
        have "(y t)\<^sup>2 \<le> s\<^sup>2" using n cw2 s2 by linarith
        thus ?thesis by (rule power2_le_imp_le) (use s0 in simp)
      qed
      have "\<bar>F' t\<bar> = (c * w t)\<^sup>2 / s * (c * \<bar>w' t\<bar>)" unfolding F'_def s_def[symmetric]
        using s0 c0 by (simp add: abs_mult)
      also have "... \<le> (w t)\<^sup>2 / s * (c * (G * y t))"
      proof (rule mult_mono)
        show "(c * w t)\<^sup>2 / s \<le> (w t)\<^sup>2 / s" using cw2 s0 by (simp add: divide_right_mono)
        show "c * \<bar>w' t\<bar> \<le> c * (G * y t)" using wb c0 by (rule mult_left_mono)
        show "0 \<le> (w t)\<^sup>2 / s" using s0 by simp
        show "0 \<le> c * \<bar>w' t\<bar>" using c0 by simp
      qed
      also have "... \<le> (w t)\<^sup>2 / s * (1 * (G * s))"
      proof (rule mult_left_mono)
        show "c * (G * y t) \<le> 1 * (G * s)" using c1 ys G y0 by (intro mult_mono) auto
        show "0 \<le> (w t)\<^sup>2 / s" using s0 by simp
      qed
      also have "... = G * (w t)\<^sup>2" using s0 by (simp add: field_simps)
      finally show "(F has_real_derivative F' t) (at t) \<and> \<bar>F' t\<bar> \<le> G * (w t)\<^sup>2" using dF by simp
    qed
    thus "\<bar>Phi (c * w T) - Phi (c * w 0)\<bar> \<le> G * integral {0..T} (\<lambda>t. (w t)\<^sup>2)"
      unfolding F_def using integral_cmul by simp
  qed
  define cn where "cn = (\<lambda>n::nat. 1 - 1 / (real n + 2))"
  have cn_t: "cn \<longlonglongrightarrow> 1" unfolding cn_def
  proof -
    have "(\<lambda>n::nat. 1 / (real n + 2)) \<longlonglongrightarrow> 0"
      by (rule real_tendsto_divide_at_top[OF tendsto_const])
         (subst add.commute, rule filterlim_tendsto_add_at_top[OF tendsto_const filterlim_real_sequentially])
    from tendsto_diff[OF tendsto_const this] show "(\<lambda>n. 1 - 1 / (real n + 2)) \<longlonglongrightarrow> 1" by simp
  qed
  have cn01: "\<And>n. 0 \<le> cn n \<and> cn n < 1" unfolding cn_def by (auto simp: field_simps)
  have lim: "\<And>a. 0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> (\<lambda>n. Phi (cn n * a)) \<longlonglongrightarrow> Phi a"
  proof -
    fix a :: real assume a0: "0 \<le> a" and a1: "a \<le> 1"
    have "(\<lambda>n. cn n * a) \<longlonglongrightarrow> 1 * a" by (intro tendsto_intros cn_t)
    hence t1: "(\<lambda>n. cn n * a) \<longlonglongrightarrow> a" by simp
    have ev: "\<forall>\<^sub>F n in sequentially. cn n * a \<in> {0..1}"
    proof (rule eventuallyI)
      fix n
      have "cn n * a \<le> 1 * 1" by (rule mult_mono) (use cn01[of n] a0 a1 in auto)
      moreover have "0 \<le> cn n * a" using cn01[of n] a0 by simp
      ultimately show "cn n * a \<in> {0..1}" by simp
    qed
    have al: "a \<in> {0..1}" using a0 a1 by simp
    from continuous_on_tendsto_compose[OF Phi_cont t1 al ev] show "(\<lambda>n. Phi (cn n * a)) \<longlonglongrightarrow> Phi a" by simp
  qed
  have wT: "0 \<le> w T" "w T \<le> 1" and w00: "0 \<le> w 0" "w 0 \<le> 1" using nrm w1 T by auto
  have "(\<lambda>n. \<bar>Phi (cn n * w T) - Phi (cn n * w 0)\<bar>) \<longlonglongrightarrow> \<bar>Phi (w T) - Phi (w 0)\<bar>"
    by (intro tendsto_intros lim wT w00)
  thus ?thesis by (rule LIMSEQ_le_const2) (use bound cn01 in auto)
qed


theorem endpoint_occupation_ac:
  fixes x z y x' z' :: "real \<Rightarrow> real" and G T :: real and S :: "real set"
  assumes T: "0 < T" and G: "0 < G" and S: "negligible S"
    and xac: "absolutely_continuous_on {0..T} x" and zac: "absolutely_continuous_on {0..T} z" and yc: "continuous_on {0..T} y"
    and nrm: "\<forall>t\<in>{0..T}. 0 \<le> x t \<and> 0 \<le> z t \<and> 0 \<le> y t \<and> (x t)\<^sup>2 + (y t)\<^sup>2 + (z t)\<^sup>2 \<le> 1"
    and bd: "x 0 = 1" "x T = 0" "z 0 = 0" "z T = 1"
    and der: "\<forall>t\<in>{0<..<T} - S. (x has_real_derivative x' t) (at t) \<and> (z has_real_derivative z' t) (at t)
      \<and> \<bar>x' t\<bar> \<le> G * y t \<and> \<bar>z' t\<bar> \<le> G * y t"
  shows "pi / 2 \<le> G * integral {0..T} (\<lambda>t. (x t)\<^sup>2 + (z t)\<^sup>2)"
proof -
  have xc: "continuous_on {0..T} x"
    by (rule absolutely_continuous_on_imp_continuous[OF xac]) simp
  have zc: "continuous_on {0..T} z"
    by (rule absolutely_continuous_on_imp_continuous[OF zac]) simp
  have nx: "\<forall>t\<in>{0..T}. 0 \<le> x t \<and> 0 \<le> y t \<and> (x t)\<^sup>2 + (y t)\<^sup>2 \<le> 1"
  proof
    fix t assume t: "t \<in> {0..T}"
    from nrm t have "0 \<le> x t" "0 \<le> y t" "(x t)\<^sup>2 + (y t)\<^sup>2 + (z t)\<^sup>2 \<le> 1" by auto
    moreover have "0 \<le> (z t)\<^sup>2" by simp
    ultimately show "0 \<le> x t \<and> 0 \<le> y t \<and> (x t)\<^sup>2 + (y t)\<^sup>2 \<le> 1" by linarith
  qed
  have nz: "\<forall>t\<in>{0..T}. 0 \<le> z t \<and> 0 \<le> y t \<and> (z t)\<^sup>2 + (y t)\<^sup>2 \<le> 1"
  proof
    fix t assume t: "t \<in> {0..T}"
    from nrm t have "0 \<le> z t" "0 \<le> y t" "(x t)\<^sup>2 + (y t)\<^sup>2 + (z t)\<^sup>2 \<le> 1" by auto
    moreover have "0 \<le> (x t)\<^sup>2" by simp
    ultimately show "0 \<le> z t \<and> 0 \<le> y t \<and> (z t)\<^sup>2 + (y t)\<^sup>2 \<le> 1" by linarith
  qed
  have ex: "\<bar>Phi (x T) - Phi (x 0)\<bar> \<le> G * integral {0..T} (\<lambda>t. (x t)\<^sup>2)"
    by (rule endpoint_window_ac[OF T G S xac yc nx]) (use der in auto)
  have ez: "\<bar>Phi (z T) - Phi (z 0)\<bar> \<le> G * integral {0..T} (\<lambda>t. (z t)\<^sup>2)"
    by (rule endpoint_window_ac[OF T G S zac yc nz]) (use der in auto)
  have x2: "(\<lambda>t. (x t)\<^sup>2) integrable_on {0..T}" using xc by (intro integrable_continuous_real continuous_intros)
  have z2: "(\<lambda>t. (z t)\<^sup>2) integrable_on {0..T}" using zc by (intro integrable_continuous_real continuous_intros)
  have "integral {0..T} (\<lambda>t. (x t)\<^sup>2 + (z t)\<^sup>2) = integral {0..T} (\<lambda>t. (x t)\<^sup>2) + integral {0..T} (\<lambda>t. (z t)\<^sup>2)"
    by (rule integral_add[OF x2 z2])
  moreover have "\<bar>Phi (x T) - Phi (x 0)\<bar> = pi / 4"
  proof -
    have "Phi (x T) - Phi (x 0) = - (pi / 4)" using bd Phi_values by simp
    thus ?thesis by simp
  qed
  moreover have "\<bar>Phi (z T) - Phi (z 0)\<bar> = pi / 4"
  proof -
    have h: "Phi (z T) - Phi (z 0) = pi / 4" using bd Phi_values by simp
    show ?thesis unfolding h using pi_gt_zero by simp
  qed
  ultimately show ?thesis using ex ez by (simp add: algebra_simps)
qed


end
