(*  Title:      Relay_Windows.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Dissipative windows of the relay: comparison bounds for an emitter amplitude decaying under a one-sided
    derivative bound, for a receiver amplitude run backwards from the final time, and the norm chain.
*)
theory Relay_Windows
  imports "HOL-Analysis.Analysis"
begin

text \<open>Comparison bounds for a scalar function whose derivative is bounded on one side.\<close>

lemma ftc_nonpos:
  fixes F F' :: "real \<Rightarrow> real" and a b :: real and S :: "real set"
  assumes S: "countable S" and ab: "a \<le> b"
    and Fc: "continuous_on {a..b} F"
    and der: "\<And>t. t \<in> {a<..<b} - S \<Longrightarrow> (F has_real_derivative F' t) (at t) \<and> F' t \<le> 0"
  shows "F b \<le> F a"
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
  have z: "((\<lambda>t::real. 0::real) has_integral 0) {a..b}" by simp
  have fle: "\<And>t. t \<in> {a..b} \<Longrightarrow> f t \<le> 0"
  proof -
    fix t assume t: "t \<in> {a..b}"
    show "f t \<le> 0"
    proof (cases "t \<in> {a<..<b} - S")
      case True
      hence "f t = F' t" unfolding f_def by (rule if_P)
      thus ?thesis using der[OF True] by simp
    next
      case False
      hence "f t = 0" unfolding f_def by (rule if_not_P)
      thus ?thesis by simp
    qed
  qed
  have "F b - F a \<le> 0" by (rule has_integral_le[OF ftc z fle])
  thus ?thesis by simp
qed

definition Qint :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "Qint g u = integral {-1..u} g"

lemma Qint_deriv:
  fixes g :: "real \<Rightarrow> real" and u :: real
  assumes gc: "continuous_on UNIV g" and u: "-1 < u" "u < 2"
  shows "(Qint g has_real_derivative g u) (at u)"
proof -
  have gc': "continuous_on {-1..2} g" using gc by (rule continuous_on_subset) simp
  have uin: "u \<in> {-1..2}" using u by simp
  have "((\<lambda>v. integral {-1..v} g) has_vector_derivative g u) (at u within {-1..2})"
    by (rule integral_has_vector_derivative[OF gc' uin])
  moreover have "{-1<..<2::real} \<subseteq> {-1..2}" by auto
  ultimately have h2: "((\<lambda>v. integral {-1..v} g) has_vector_derivative g u) (at u within {-1<..<2})"
    by (rule has_vector_derivative_within_subset)
  have uo: "u \<in> {-1<..<2}" using u by simp
  have "at u within {-1<..<2} = at u" by (rule at_within_open[OF uo open_greaterThanLessThan])
  hence "((\<lambda>v. integral {-1..v} g) has_vector_derivative g u) (at u)" using h2 by simp
  thus ?thesis unfolding Qint_def by (simp add: has_real_derivative_iff_has_vector_derivative)
qed

lemma Qint_cont:
  fixes g :: "real \<Rightarrow> real"
  assumes gc: "continuous_on UNIV g"
  shows "continuous_on {-1<..<2} (Qint g)"
proof (rule continuous_at_imp_continuous_on, intro ballI)
  fix u :: real assume u: "u \<in> {-1<..<2}"
  have u1: "-1 < u" and u2: "u < 2" using u by auto
  have dd: "(Qint g has_real_derivative g u) (at u)" by (rule Qint_deriv[OF gc u1 u2])
  show "isCont (Qint g) u" using DERIV_continuous[OF dd] by (simp add: isCont_def continuous_at)
qed

lemma Qint_split:
  fixes g :: "real \<Rightarrow> real" and a u :: real
  assumes gc: "continuous_on UNIV g" and a: "-1 \<le> a" and au: "a \<le> u"
  shows "integral {a..u} g = Qint g u - Qint g a"
proof -
  have "g integrable_on {-1..u}" using gc by (intro integrable_continuous_real continuous_on_subset[OF gc]) simp
  from Henstock_Kurzweil_Integration.integral_combine[OF a au this] show ?thesis unfolding Qint_def by simp
qed

text \<open>Core comparison lemma: s * Q(y t) - t is non-increasing when s * g(y) * y' <= 1.\<close>

lemma comp_window:
  fixes g y y' :: "real \<Rightarrow> real" and s a b :: real and S :: "real set"
  assumes S: "countable S" and ab: "a \<le> b" and gc: "continuous_on UNIV g"
    and yc: "continuous_on {a..b} y" and rng: "\<And>t. t \<in> {a..b} \<Longrightarrow> -1 < y t \<and> y t < 2"
    and der: "\<And>t. t \<in> {a<..<b} - S \<Longrightarrow> (y has_real_derivative y' t) (at t) \<and> s * (g (y t) * y' t) \<le> 1"
  shows "s * Qint g (y b) - b \<le> s * Qint g (y a) - a"
proof -
  define F where "F = (\<lambda>t. s * Qint g (y t) - t)"
  have sub: "y ` {a..b} \<subseteq> {-1<..<2}" using rng by auto
  have Fc: "continuous_on {a..b} F" unfolding F_def
    by (intro continuous_intros continuous_on_compose2[OF Qint_cont[OF gc] yc sub])
  have "F b \<le> F a"
  proof (rule ftc_nonpos[where F' = "\<lambda>t. s * (g (y t) * y' t) - 1", OF S ab Fc])
    fix t assume t: "t \<in> {a<..<b} - S"
    hence tt: "t \<in> {a..b}" by auto
    from der t have hy: "(y has_real_derivative y' t) (at t)" and cnd: "s * (g (y t) * y' t) \<le> 1" by auto
    from rng[OF tt] have r: "-1 < y t" "y t < 2" by auto
    have dQ: "(Qint g has_real_derivative g (y t)) (at (y t))" by (rule Qint_deriv[OF gc r])
    have dc: "((\<lambda>t. Qint g (y t)) has_real_derivative g (y t) * y' t) (at t)"
      using DERIV_chain2[OF dQ hy] .
    have "(F has_real_derivative s * (g (y t) * y' t) - 1) (at t)" unfolding F_def
      by (rule DERIV_diff[OF DERIV_cmult[OF dc] DERIV_ident])
    thus "(F has_real_derivative s * (g (y t) * y' t) - 1) (at t) \<and> s * (g (y t) * y' t) - 1 \<le> 0"
      using cnd by simp
  qed
  thus ?thesis unfolding F_def .
qed

section \<open>Emitter window\<close>

definition E1 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "E1 G d v = G * sqrt (1 - v\<^sup>2) + d * v"

definition Fem :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Fem G d u = integral {u..1} (\<lambda>v. 1 / (G * sqrt (1 - v\<^sup>2) + d * v))"

lemma E1_pos:
  assumes G: "0 < G" and d: "0 < d" and v: "0 \<le> v" and v1: "v \<le> 1"
  shows "0 < E1 G d v"
proof (cases "v = 0")
  case True
  thus ?thesis unfolding E1_def using G by simp
next
  case False
  hence "0 < v" using v by simp
  hence "0 < d * v" using d by simp
  moreover have "0 \<le> G * sqrt (1 - v\<^sup>2)"
  proof (rule mult_nonneg_nonneg[OF less_imp_le[OF G] real_sqrt_ge_zero])
    have "v\<^sup>2 \<le> 1" using v v1 by (simp add: power_le_one)
    thus "0 \<le> 1 - v\<^sup>2" by simp
  qed
  ultimately show ?thesis unfolding E1_def by linarith
qed

definition g1 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "g1 G d v = 1 / E1 G d (max 0 (min 1 v))"

lemma g1_cont:
  assumes G: "0 < G" and d: "0 < d"
  shows "continuous_on UNIV (g1 G d)"
proof -
  have ne: "\<And>v::real. E1 G d (max 0 (min 1 v)) \<noteq> 0"
  proof -
    fix v :: real
    have a: "0 \<le> max 0 (min 1 v)" by simp
    have b: "max 0 (min 1 v) \<le> 1" by simp
    have "0 < E1 G d (max 0 (min 1 v))" by (rule E1_pos[OF G d a b])
    thus "E1 G d (max 0 (min 1 v)) \<noteq> 0" by simp
  qed
  have h: "continuous_on UNIV (\<lambda>v::real. E1 G d (max 0 (min 1 v)))"
    unfolding E1_def by (intro continuous_intros)
  have "continuous_on UNIV (\<lambda>v::real. 1 / E1 G d (max 0 (min 1 v)))"
    by (rule continuous_on_divide[OF continuous_on_const h]) (use ne in simp)
  thus ?thesis unfolding g1_def .
qed

lemma g1_eq:
  assumes "0 \<le> v" "v \<le> 1"
  shows "g1 G d v = 1 / E1 G d v"
  using assms unfolding g1_def by simp

lemma Fem_eq:
  assumes G: "0 < G" and d: "0 < d" and u0: "0 \<le> u" and u1: "u \<le> 1"
  shows "Fem G d u = Qint (g1 G d) 1 - Qint (g1 G d) u"
proof -
  have "Fem G d u = integral {u..1} (g1 G d)" unfolding Fem_def
  proof (rule integral_cong)
    fix v assume v: "v \<in> {u..1}"
    hence "0 \<le> v" "v \<le> 1" using u0 by auto
    thus "1 / (G * sqrt (1 - v\<^sup>2) + d * v) = g1 G d v" by (simp add: g1_eq E1_def)
  qed
  also have "... = Qint (g1 G d) 1 - Qint (g1 G d) u"
    by (rule Qint_split[OF g1_cont[OF G d]]) (use u0 u1 in auto)
  finally show ?thesis .
qed

theorem emitter_window:
  fixes x x' :: "real \<Rightarrow> real" and G d T :: real and S :: "real set"
  assumes T: "0 < T" and G: "0 < G" and d: "0 < d" and S: "countable S"
    and xc: "continuous_on {0..T} x"
    and rng: "\<forall>t\<in>{0..T}. 0 \<le> x t \<and> x t \<le> 1" and x0: "x 0 = 1"
    and der: "\<forall>t\<in>{0<..<T} - S. (x has_real_derivative x' t) (at t)
        \<and> - G * sqrt (1 - (x t)\<^sup>2) - d * x t \<le> x' t"
  shows "\<forall>t\<in>{0..T}. Fem G d (x t) \<le> t"
proof
  fix t assume t: "t \<in> {0..T}"
  have gc: "continuous_on UNIV (g1 G d)" by (rule g1_cont[OF G d])
  have xc': "continuous_on {0..t} x" using xc t by (intro continuous_on_subset[OF xc]) auto
  have key: "-1 * Qint (g1 G d) (x t) - t \<le> -1 * Qint (g1 G d) (x 0) - 0"
  proof (rule comp_window[OF S _ gc xc'])
    show "0 \<le> t" using t by simp
  next
    fix r assume r: "r \<in> {0..t}"
    hence "r \<in> {0..T}" using t by auto
    thus "-1 < x r \<and> x r < 2" using rng by force
  next
    fix r assume r: "r \<in> {0<..<t} - S"
    hence rT: "r \<in> {0<..<T} - S" using t by auto
    hence rr: "r \<in> {0..T}" by auto
    from der rT have hx: "(x has_real_derivative x' r) (at r)"
      and lb: "- G * sqrt (1 - (x r)\<^sup>2) - d * x r \<le> x' r" by auto
    from rng rr have x01: "0 \<le> x r" "x r \<le> 1" by auto
    have Ep: "0 < E1 G d (x r)" by (rule E1_pos[OF G d x01])
    have "-1 * E1 G d (x r) \<le> x' r" using lb unfolding E1_def by simp
    hence "-1 \<le> x' r / E1 G d (x r)" using pos_le_divide_eq[OF Ep, of "-1" "x' r"] by simp
    hence "-1 * (g1 G d (x r) * x' r) \<le> 1" using g1_eq[OF x01] by (simp add: divide_inverse_commute algebra_simps)
    thus "(x has_real_derivative x' r) (at r) \<and> -1 * (g1 G d (x r) * x' r) \<le> 1" using hx by simp
  qed
  have x1: "0 \<le> x t" "x t \<le> 1" using rng t by auto
  have "Fem G d (x t) = Qint (g1 G d) 1 - Qint (g1 G d) (x t)" by (rule Fem_eq[OF G d x1])
  also have "... \<le> t" using key x0 by simp
  finally show "Fem G d (x t) \<le> t" .
qed

section \<open>Receiver window (backwards)\<close>

definition E2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "E2 G d v = G * sqrt (1 - v\<^sup>2) - d * v"

definition vstar :: "real \<Rightarrow> real \<Rightarrow> real" where
  "vstar G d = G / sqrt (G\<^sup>2 + d\<^sup>2)"

definition Hrec :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "Hrec G d u = integral {0..u} (\<lambda>v. 1 / (G * sqrt (1 - v\<^sup>2) - d * v))"

lemma vstar_sq:
  assumes G: "0 < G" and d: "0 < d"
  shows "(vstar G d)\<^sup>2 = G\<^sup>2 / (G\<^sup>2 + d\<^sup>2)"
proof -
  have "0 < G\<^sup>2 + d\<^sup>2" using G by (simp add: add_pos_nonneg)
  thus ?thesis unfolding vstar_def by (simp add: power_divide)
qed

lemma vstar_lt1:
  assumes G: "0 < G" and d: "0 < d"
  shows "(vstar G d)\<^sup>2 < 1"
proof -
  have p: "0 < G\<^sup>2 + d\<^sup>2" using G by (simp add: add_pos_nonneg)
  have "0 < d\<^sup>2" using d by simp
  hence "G\<^sup>2 < G\<^sup>2 + d\<^sup>2" by simp
  thus ?thesis using vstar_sq[OF G d] p by (simp add: divide_less_eq)
qed

lemma E2_pos:
  assumes G: "0 < G" and d: "0 < d" and v: "0 \<le> v" and vs: "v < vstar G d"
  shows "0 < E2 G d v"
proof -
  have p: "0 < G\<^sup>2 + d\<^sup>2" using G by (simp add: add_pos_nonneg)
  have vs0: "0 \<le> vstar G d" using G unfolding vstar_def by simp
  have v2: "v\<^sup>2 < (vstar G d)\<^sup>2" by (rule power_strict_mono[OF vs v]) simp
  hence v2s: "v\<^sup>2 < G\<^sup>2 / (G\<^sup>2 + d\<^sup>2)" using vstar_sq[OF G d] by simp
  hence v2': "v\<^sup>2 * (G\<^sup>2 + d\<^sup>2) < G\<^sup>2" using pos_less_divide_eq[OF p, of "v\<^sup>2" "G\<^sup>2"] v2s by simp
  have v1: "v\<^sup>2 < 1" using v2 vstar_lt1[OF G d] by simp
  have "(d * v)\<^sup>2 < (G * sqrt (1 - v\<^sup>2))\<^sup>2"
  proof -
    have "(G * sqrt (1 - v\<^sup>2))\<^sup>2 = G\<^sup>2 * (1 - v\<^sup>2)" using v1 by (simp add: power_mult_distrib)
    moreover have "(d * v)\<^sup>2 = d\<^sup>2 * v\<^sup>2" by (simp add: power_mult_distrib)
    ultimately show ?thesis using v2' by (simp add: algebra_simps)
  qed
  hence "d * v < G * sqrt (1 - v\<^sup>2)" proof (rule power2_less_imp_less)
    show "0 \<le> G * sqrt (1 - v\<^sup>2)"
      by (rule mult_nonneg_nonneg[OF less_imp_le[OF G] real_sqrt_ge_zero]) (use v1 in simp)
  qed
  thus ?thesis unfolding E2_def by simp
qed

definition g2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "g2 G d c v = 1 / E2 G d (max 0 (min c v))"

lemma g2_cont:
  assumes G: "0 < G" and d: "0 < d" and c0: "0 \<le> c" and c: "c < vstar G d"
  shows "continuous_on UNIV (g2 G d c)"
proof -
  have ne: "\<And>v::real. E2 G d (max 0 (min c v)) \<noteq> 0"
  proof -
    fix v :: real
    have a: "0 \<le> max 0 (min c v)" by simp
    have b: "max 0 (min c v) \<le> c" using c0 by simp
    have "0 < E2 G d (max 0 (min c v))" by (rule E2_pos[OF G d a]) (use b c in linarith)
    thus "E2 G d (max 0 (min c v)) \<noteq> 0" by simp
  qed
  have h: "continuous_on UNIV (\<lambda>v::real. E2 G d (max 0 (min c v)))"
    unfolding E2_def by (intro continuous_intros)
  have "continuous_on UNIV (\<lambda>v::real. 1 / E2 G d (max 0 (min c v)))"
    by (rule continuous_on_divide[OF continuous_on_const h]) (use ne in simp)
  thus ?thesis unfolding g2_def .
qed

lemma g2_eq:
  assumes "0 \<le> v" "v \<le> c" "0 \<le> c"
  shows "g2 G d c v = 1 / E2 G d v"
  using assms unfolding g2_def by simp

lemma Hrec_eq:
  assumes G: "0 < G" and d: "0 < d" and c0: "0 \<le> c" and c: "c < vstar G d" and u0: "0 \<le> u" and uc: "u \<le> c"
  shows "Hrec G d u = Qint (g2 G d c) u - Qint (g2 G d c) 0"
proof -
  have "Hrec G d u = integral {0..u} (g2 G d c)" unfolding Hrec_def
  proof (rule integral_cong)
    fix v assume v: "v \<in> {0..u}"
    hence "0 \<le> v" "v \<le> c" using uc by auto
    thus "1 / (G * sqrt (1 - v\<^sup>2) - d * v) = g2 G d c v" using c0 by (simp add: g2_eq E2_def)
  qed
  also have "... = Qint (g2 G d c) u - Qint (g2 G d c) 0"
    by (rule Qint_split[OF g2_cont[OF G d c0 c]]) (use u0 in auto)
  finally show ?thesis .
qed

theorem receiver_window:
  fixes z z' :: "real \<Rightarrow> real" and G d T c :: real and S :: "real set"
  assumes T: "0 < T" and G: "0 < G" and d: "0 < d" and S: "countable S"
    and zc: "continuous_on {0..T} z"
    and nn: "\<forall>t\<in>{0..T}. 0 \<le> z t" and z0: "z 0 = 0"
    and barrier: "\<forall>t\<in>{0..T}. z t \<le> c" and cv: "c < vstar G d"
    and der: "\<forall>t\<in>{0<..<T} - S. (z has_real_derivative z' t) (at t)
        \<and> z' t \<le> G * sqrt (1 - (z t)\<^sup>2) - d * z t"
  shows "Hrec G d (z T) \<le> T"
    and "\<forall>t\<in>{0..T}. Hrec G d (z T) - Hrec G d (z t) \<le> T - t"
proof -
  have c0: "0 \<le> c"
  proof -
    have "z 0 \<le> c" using barrier T by auto
    thus ?thesis using z0 by simp
  qed
  have gc: "continuous_on UNIV (g2 G d c)" by (rule g2_cont[OF G d c0 cv])
  have win: "\<forall>t\<in>{0..T}. Hrec G d (z T) - Hrec G d (z t) \<le> T - t"
  proof
    fix t assume t: "t \<in> {0..T}"
    have zc': "continuous_on {t..T} z" using zc t by (intro continuous_on_subset[OF zc]) auto
    have key: "1 * Qint (g2 G d c) (z T) - T \<le> 1 * Qint (g2 G d c) (z t) - t"
    proof (rule comp_window[OF S _ gc zc'])
      show "t \<le> T" using t by simp
    next
      fix r assume r: "r \<in> {t..T}"
      hence "r \<in> {0..T}" using t by auto
      hence "0 \<le> z r" "z r \<le> c" using nn barrier by auto
      have "vstar G d < 1"
      proof (rule power2_less_imp_less)
        show "(vstar G d)\<^sup>2 < 1\<^sup>2" using vstar_lt1[OF G d] by simp
      qed simp
      thus "-1 < z r \<and> z r < 2" using \<open>0 \<le> z r\<close> \<open>z r \<le> c\<close> cv by linarith
    next
      fix r assume r: "r \<in> {t<..<T} - S"
      hence rT: "r \<in> {0<..<T} - S" using t by auto
      hence rr: "r \<in> {0..T}" by auto
      from der rT have hz: "(z has_real_derivative z' r) (at r)"
        and ub: "z' r \<le> G * sqrt (1 - (z r)\<^sup>2) - d * z r" by auto
      from nn barrier rr have z01: "0 \<le> z r" "z r \<le> c" by auto
      have Ep: "0 < E2 G d (z r)" by (rule E2_pos[OF G d z01(1)]) (use z01(2) cv in linarith)
      have "z' r \<le> E2 G d (z r)" using ub unfolding E2_def by simp
      hence "z' r / E2 G d (z r) \<le> 1" using Ep by (simp add: divide_le_eq)
      hence "1 * (g2 G d c (z r) * z' r) \<le> 1" using g2_eq[OF z01(1) z01(2) c0] by (simp add: divide_inverse_commute algebra_simps)
      thus "(z has_real_derivative z' r) (at r) \<and> 1 * (g2 G d c (z r) * z' r) \<le> 1" using hz by simp
    qed
    have zt: "0 \<le> z t" "z t \<le> c" using nn barrier t by auto
    have zT: "0 \<le> z T" "z T \<le> c" using nn barrier T by auto
    have "Hrec G d (z T) - Hrec G d (z t) = Qint (g2 G d c) (z T) - Qint (g2 G d c) (z t)"
      using Hrec_eq[OF G d c0 cv zT] Hrec_eq[OF G d c0 cv zt] by simp
    also have "... \<le> T - t" using key by simp
    finally show "Hrec G d (z T) - Hrec G d (z t) \<le> T - t" .
  qed
  thus "\<forall>t\<in>{0..T}. Hrec G d (z T) - Hrec G d (z t) \<le> T - t" .
  have "Hrec G d (z T) - Hrec G d (z 0) \<le> T - 0" using win T by force
  moreover have "Hrec G d (z 0) = 0" unfolding Hrec_def z0 by simp
  ultimately show "Hrec G d (z T) \<le> T" by simp
qed

section \<open>Norm corollary\<close>

corollary norm_chain:
  fixes x z :: "real \<Rightarrow> real" and T a b n \<Delta> :: real
  assumes xc: "continuous_on {0..T} x" and zc: "continuous_on {0..T} z"
    and a: "a \<le> integral {0..T} (\<lambda>t. (x t)\<^sup>2)" and b: "b \<le> integral {0..T} (\<lambda>t. (z t)\<^sup>2)"
    and n: "n \<le> 1 - \<Delta> * integral {0..T} (\<lambda>t. (x t)\<^sup>2 + (z t)\<^sup>2)" and D: "0 \<le> \<Delta>"
    and zn: "(z T)\<^sup>2 \<le> n"
  shows "(z T)\<^sup>2 + \<Delta> * (a + b) \<le> 1"
proof -
  have x2: "(\<lambda>t. (x t)\<^sup>2) integrable_on {0..T}" using xc by (intro integrable_continuous_real continuous_intros)
  have z2: "(\<lambda>t. (z t)\<^sup>2) integrable_on {0..T}" using zc by (intro integrable_continuous_real continuous_intros)
  have sp: "integral {0..T} (\<lambda>t. (x t)\<^sup>2 + (z t)\<^sup>2) = integral {0..T} (\<lambda>t. (x t)\<^sup>2) + integral {0..T} (\<lambda>t. (z t)\<^sup>2)"
    by (rule integral_add[OF x2 z2])
  have "\<Delta> * (a + b) \<le> \<Delta> * integral {0..T} (\<lambda>t. (x t)\<^sup>2 + (z t)\<^sup>2)"
    unfolding sp by (rule mult_left_mono) (use a b D in auto)
  thus ?thesis using zn n by linarith
qed

end
