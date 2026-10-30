(*  Title:      Zielinski_Zych.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    The Zielinski--Zych speed limits for every exponent 0 < a <= 1 and their limit a -> 0.

    For a discrete spectral measure with populations p n >= 0, sum p n = 1, energies E n >= E0
    and fractional moment M_a = sum p n (E n - E0)^a, if the autocorrelation vanishes at tau >= 0
    then pi^a <= 2 M_a tau^a (Zielinski--Zych, Phys. Rev. A 74, 034301 (2006), Eq. (10)).
    The case a = 1 is the Margolus--Levitin bound.
*)

theory Zielinski_Zych
  imports "HOL-Analysis.Analysis"
begin

section \<open>Numerical bounds on pi\<close>

lemma pi_lo: "157/50 < pi"
  by (rule less_le_trans[OF _ pi_approx(1)]) simp

lemma pi_hi: "pi < 63/20"
  by (rule le_less_trans[OF pi_approx(2)]) simp

section \<open>Elementary trigonometric bounds\<close>

lemma cos_ge_one_minus_sq:
  fixes x :: real
  shows "1 - x\<^sup>2 / 2 \<le> cos x"
proof -
  have h1: "cos x = 1 - 2 * (sin (x/2))\<^sup>2"
    using cos_double_sin[of "x/2"] by simp
  have h2: "(sin (x/2))\<^sup>2 \<le> (x/2)\<^sup>2"
    by (rule iffD1[OF abs_le_square_iff abs_sin_x_le_abs_x])
  have h3: "(x/2)\<^sup>2 = x\<^sup>2 / 4" by (simp add: power_divide)
  show ?thesis using h1 h2 h3 by linarith
qed

lemma sin_ge_sub_cube:
  fixes x :: real
  assumes x0: "0 \<le> x"
  shows "x - x ^ 3 / 6 \<le> sin x"
proof -
  let ?f = "\<lambda>y::real. sin y - y + y ^ 3 / 6"
  have "?f 0 \<le> ?f x"
  proof (rule DERIV_nonneg_imp_nondecreasing[OF x0])
    fix y :: real
    assume "0 \<le> y" "y \<le> x"
    have d: "DERIV ?f y :> cos y - 1 + y\<^sup>2 / 2"
      by (auto intro!: derivative_eq_intros simp: field_simps)
    have "0 \<le> cos y - 1 + y\<^sup>2 / 2" using cos_ge_one_minus_sq[of y] by simp
    thus "\<exists>d. DERIV ?f y :> d \<and> 0 \<le> d" using d by blast
  qed
  thus ?thesis by simp
qed

text \<open>Jordan's inequality on \<open>[0, pi/2]\<close>, from the convexity of \<open>- sin\<close> on \<open>[0, pi]\<close>.\<close>

lemma jordan:
  assumes x0: "0 \<le> x" and x1: "x \<le> pi/2"
  shows "2 / pi * x \<le> sin x"
proof -
  have pp: "0 < pi" by simp
  have cv: "convex_on {0..pi} (\<lambda>x. - sin x)"
  proof (rule convex_on_realI[where f' = "\<lambda>x. - cos x"])
    show "connected {0..pi}" by (rule connected_Icc)
  next
    fix x :: real
    assume "x \<in> {0..pi}"
    show "((\<lambda>x. - sin x) has_real_derivative - cos x) (at x)"
      by (auto intro!: derivative_eq_intros)
  next
    fix x y :: real
    assume "x \<in> {0..pi}" "y \<in> {0..pi}" "x \<le> y"
    hence "cos y \<le> cos x" using cos_monotone_0_pi_le[of x y] by simp
    thus "- cos x \<le> - cos y" by simp
  qed
  define t where "t = 2 / pi * x"
  have t0: "0 \<le> t" unfolding t_def using pp x0 by simp
  have t1: "t \<le> 1"
  proof -
    have "2 / pi * x \<le> 2 / pi * (pi/2)" using x1 pp by (intro mult_left_mono) auto
    also have "\<dots> = 1" using pp by simp
    finally show ?thesis unfolding t_def .
  qed
  have m1: "(0::real) \<in> {0..pi}" using pp by simp
  have m2: "pi/2 \<in> {0..pi}" using pp by simp
  note h = convex_onD[OF cv t0 t1 m1 m2]
  have e: "t * (pi/2) = x" unfolding t_def using pp by simp
  have "- sin ((1 - t) *\<^sub>R 0 + t *\<^sub>R (pi/2)) \<le> (1 - t) * (- sin 0) + t * (- sin (pi/2))"
    using h .
  hence "- sin (t * (pi/2)) \<le> - t" by (simp add: real_scaleR_def)
  hence "t \<le> sin (t * (pi/2))" by simp
  thus ?thesis unfolding e t_def by simp
qed

lemma P_small:
  assumes h0: "0 \<le> v" and hv: "v \<le> pi / 2"
  shows "0 \<le> pi\<^sup>2 * (sin (v/2))\<^sup>2 - pi * v + (pi - v) * sin v"
proof -
  note hp1 = pi_lo
  note hp2 = pi_hi
  have pp: "0 < pi" by simp
  have hv': "v \<le> 63/40" using hv hp2 by linarith
  have ha: "v/2 - (v/2) ^ 3 / 6 \<le> sin (v/2)" by (rule sin_ge_sub_cube) (use h0 in simp)
  have hb: "v - v ^ 3 / 6 \<le> sin v" by (rule sin_ge_sub_cube) (use h0 in simp)
  have hv2: "v\<^sup>2 \<le> 3"
  proof -
    have "v\<^sup>2 \<le> (63/40)\<^sup>2" by (rule power_mono[OF hv' h0])
    thus ?thesis by (simp add: eval_nat_numeral)
  qed
  have hl: "0 \<le> v/2 - (v/2) ^ 3 / 6"
  proof -
    have "0 \<le> v * (3 - v\<^sup>2)" using h0 hv2 by (intro mult_nonneg_nonneg) auto
    moreover have "(v/2) ^ 3 = v ^ 3 / 8" by (simp add: power_divide)
    moreover have "v * (3 - v\<^sup>2) = 3 * v - v ^ 3"
      by (simp add: algebra_simps power2_eq_square power3_eq_cube)
    ultimately show ?thesis using h0 by linarith
  qed
  have ha2: "(v/2 - (v/2) ^ 3 / 6)\<^sup>2 \<le> (sin (v/2))\<^sup>2" by (rule power_mono[OF ha hl])
  have hpv: "0 \<le> pi - v" using hv pp by linarith
  have hA0: "0 \<le> pi * v" using pp h0 by simp
  have hA: "pi * v \<le> 497/100"
  proof -
    have "pi * v \<le> (63/20) * (63/40)"
      by (rule mult_mono) (use hp2 hv' h0 in auto)
    thus ?thesis by simp
  qed
  have hA2: "(pi * v)\<^sup>2 \<le> 25"
  proof -
    have "(pi * v)\<^sup>2 \<le> (497/100)\<^sup>2" by (rule power_mono[OF hA hA0])
    thus ?thesis by (simp add: eval_nat_numeral)
  qed
  have hpp: "197/20 \<le> pi\<^sup>2"
  proof -
    have c1: "(157/50)\<^sup>2 \<le> pi\<^sup>2" by (rule power_mono) (use hp1 in auto)
    have c2: "(197/20::real) \<le> (157/50)\<^sup>2" by (simp add: eval_nat_numeral)
    show ?thesis using c1 c2 by linarith
  qed
  have hR: "0 \<le> pi\<^sup>2 / 4 - 1 - pi * v / 6 - (pi * v)\<^sup>2 / 48" using hA hA2 hpp by linarith
  have key: "pi\<^sup>2 * (v/2 - (v/2) ^ 3 / 6)\<^sup>2 - pi * v + (pi - v) * (v - v ^ 3 / 6)
      = v\<^sup>2 * (pi\<^sup>2 / 4 - 1 - pi * v / 6 - (pi * v)\<^sup>2 / 48)
        + (v ^ 4 / 6 + pi\<^sup>2 * v ^ 6 / 2304)"
    by (simp add: power_divide field_simps power2_eq_square) algebra
  have h3: "0 \<le> v\<^sup>2 * (pi\<^sup>2 / 4 - 1 - pi * v / 6 - (pi * v)\<^sup>2 / 48)
        + (v ^ 4 / 6 + pi\<^sup>2 * v ^ 6 / 2304)"
  proof -
    have "0 \<le> v\<^sup>2 * (pi\<^sup>2 / 4 - 1 - pi * v / 6 - (pi * v)\<^sup>2 / 48)"
      using hR by (intro mult_nonneg_nonneg) auto
    moreover have "0 \<le> v ^ 4 / 6 + pi\<^sup>2 * v ^ 6 / 2304" using h0 by simp
    ultimately show ?thesis by linarith
  qed
  have f1: "pi\<^sup>2 * (v/2 - (v/2) ^ 3 / 6)\<^sup>2 \<le> pi\<^sup>2 * (sin (v/2))\<^sup>2"
    by (rule mult_left_mono[OF ha2]) simp
  have f2: "(pi - v) * (v - v ^ 3 / 6) \<le> (pi - v) * sin v"
    by (rule mult_left_mono[OF hb hpv])
  show ?thesis using f1 f2 key h3 by linarith
qed

lemma P_large:
  assumes h0: "pi / 2 \<le> v" and hv: "v \<le> pi"
  shows "0 \<le> pi\<^sup>2 * (sin (v/2))\<^sup>2 - pi * v + (pi - v) * sin v"
proof -
  note hp1 = pi_lo
  note hp2 = pi_hi
  have pp: "0 < pi" by simp
  obtain w where wd: "w = pi - v" by blast
  have vw: "v = pi - w" using wd by simp
  have w0: "0 \<le> w" using wd hv by simp
  have w1: "w \<le> pi / 2" using wd h0 by simp
  have hcv: "cos v = - cos w" using vw by simp
  have hcw: "cos w = 1 - 2 * (sin (w/2))\<^sup>2" using cos_double_sin[of "w/2"] by simp
  have hcv2: "cos v = 1 - 2 * (sin (v/2))\<^sup>2" using cos_double_sin[of "v/2"] by simp
  have hs: "(sin (v/2))\<^sup>2 = 1 - (sin (w/2))\<^sup>2" using hcv hcw hcv2 by linarith
  have hsv: "sin v = sin w" using vw by simp
  have s0: "0 \<le> sin (w/2)" by (rule sin_ge_zero) (use w0 w1 pp in linarith)+
  have s1: "sin (w/2) \<le> w/2" by (rule sin_x_le_x) (use w0 in simp)
  have s2: "(sin (w/2))\<^sup>2 \<le> (w/2)\<^sup>2" by (rule power_mono[OF s1 s0])
  have hj: "2 / pi * w \<le> sin w" by (rule jordan[OF w0 w1])
  have hsw: "2 * w \<le> pi * sin w"
  proof -
    have "pi * (2 / pi * w) \<le> pi * sin w" by (rule mult_left_mono[OF hj]) (use pp in simp)
    moreover have "pi * (2 / pi * w) = 2 * w" using pp by simp
    ultimately show ?thesis by simp
  qed
  have p3: "(157/50::real) ^ 3 \<le> pi ^ 3" by (rule power_mono) (use hp1 in auto)
  have p3': "(157/50::real) ^ 3 \<ge> 309/10" by (simp add: eval_nat_numeral)
  have p2: "(157/50::real) ^ 2 \<le> pi ^ 2" by (rule power_mono) (use hp1 in auto)
  have p2': "(157/50::real) ^ 2 \<ge> 197/20" by (simp add: eval_nat_numeral)
  have p4: "pi ^ 4 \<le> (63/20::real) ^ 4" by (rule power_mono) (use hp2 pp in auto)
  have p4': "(63/20::real) ^ 4 \<le> 197/2" by (simp add: eval_nat_numeral)
  have hK: "0 \<le> (pi / 2 - w) * (pi ^ 3 / 4 - 2)"
    by (rule mult_nonneg_nonneg) (use w1 p3 p3' in linarith)+
  have ex: "(pi / 2 - w) * (pi ^ 3 / 4 - 2) = pi ^ 4 / 8 - pi - pi ^ 3 * w / 4 + 2 * w"
    by (simp add: field_simps eval_nat_numeral)
  have h3: "0 \<le> pi\<^sup>2 - pi ^ 3 * w / 4 + 2 * w" using hK ex p2 p2' p4 p4' hp1 by linarith
  have f1: "pi ^ 3 * (sin (w/2))\<^sup>2 \<le> pi ^ 3 * (w/2)\<^sup>2" by (rule mult_left_mono[OF s2]) (use pp in simp)
  have f2: "w * (2 * w) \<le> w * (pi * sin w)" by (rule mult_left_mono[OF hsw w0])
  have f4: "0 \<le> w * (pi\<^sup>2 - pi ^ 3 * w / 4 + 2 * w)" by (rule mult_nonneg_nonneg[OF w0 h3])
  have e1: "pi - v = w" using wd by simp
  have e2: "pi * v = pi * pi - pi * w" unfolding vw by (simp add: algebra_simps)
  have a1: "pi\<^sup>2 * (sin (v/2))\<^sup>2 = pi\<^sup>2 * (1 - (sin (w/2))\<^sup>2)" by (simp add: hs)
  have a2: "(pi - v) * sin v = w * sin w" by (simp add: e1 hsv)
  have ge: "pi\<^sup>2 * (sin (v/2))\<^sup>2 - pi * v + (pi - v) * sin v
      = - (pi\<^sup>2 * (sin (w/2))\<^sup>2) + pi * w + w * sin w"
    using a1 a2 e2 by (simp add: power2_eq_square algebra_simps)
  show ?thesis
  proof (rule ccontr)
    assume nn: "\<not> 0 \<le> pi\<^sup>2 * (sin (v/2))\<^sup>2 - pi * v + (pi - v) * sin v"
    hence neg: "- (pi\<^sup>2 * (sin (w/2))\<^sup>2) + pi * w + w * sin w < 0" using ge by simp
    have "pi * (- (pi\<^sup>2 * (sin (w/2))\<^sup>2) + pi * w + w * sin w) < 0"
      using pp neg by (rule mult_pos_neg)
    moreover have idn: "pi * (- (pi\<^sup>2 * (sin (w/2))\<^sup>2) + pi * w + w * sin w)
        = (pi ^ 3 * (w / 2)\<^sup>2 - pi ^ 3 * (sin (w/2))\<^sup>2)
          + w * (pi\<^sup>2 - pi ^ 3 * w / 4 + 2 * w) + (w * (pi * sin w) - w * (2 * w))"
      by (simp add: field_simps power2_eq_square eval_nat_numeral)
    ultimately show False using f1 f2 f4 by linarith
  qed
qed

lemma P_nonneg:
  assumes "0 \<le> v" and "v \<le> pi"
  shows "0 \<le> pi\<^sup>2 * (sin (v/2))\<^sup>2 - pi * v + (pi - v) * sin v"
  using assms P_small P_large by (cases "v \<le> pi / 2") auto

section \<open>Power bounds\<close>

lemma rpow_hm:
  fixes t a :: real
  assumes ht: "0 < t" and a0: "0 \<le> a" and a1: "a \<le> 1"
  shows "t \<le> t powr a * (t + a * (1 - t))"
proof -
  have tne: "t \<noteq> 0" by (rule not_sym[OF less_imp_neq[OF ht]])
  have q: "0 < t powr a" using tne by simp
  have Y: "(1/t) powr a * 1 powr (1 - a) \<le> a * (1/t) + (1 - a) * 1"
    by (rule Youngs_inequality_0) (use ht a0 a1 in auto)
  have e1: "(1/t) powr a = 1 / t powr a" by (simp add: powr_divide)
  have Y2: "1 / t powr a \<le> a * (1/t) + (1 - a)" using Y e1 by simp
  have tq: "0 \<le> t * t powr a" using ht q by simp
  note h2 = mult_right_mono[OF Y2 tq]
  have l: "1 / t powr a * (t * t powr a) = t" using ht q by (simp add: field_simps)
  have r: "(a * (1/t) + (1 - a)) * (t * t powr a) = t powr a * (t + a * (1 - t))"
    using ht by (simp add: field_simps)
  show ?thesis using h2[unfolded l r] .
qed

section \<open>The normalized inequality\<close>

lemma zz_aux_le:
  assumes a0: "0 < a" and a1: "a \<le> 1" and t0: "0 \<le> t" and t1: "t \<le> 1"
  shows "0 \<le> t powr a - (1 - cos (pi * t)) / 2 + a / pi * sin (pi * t)"
proof -
  have pp: "0 < pi" by simp
  have pne: "pi \<noteq> 0" by simp
  obtain v where vd: "v = pi * (1 - t)" by blast
  have v0: "0 \<le> v" unfolding vd by (rule mult_nonneg_nonneg) (use pp t1 in auto)
  have pt0: "0 \<le> pi * t" using pp t0 by simp
  have vpi: "v \<le> pi" using vd pt0 by (simp add: algebra_simps)
  have hpt: "pi * t = pi - v" using vd by (simp add: algebra_simps)
  have hcos: "cos (pi * t) = - cos v" unfolding hpt by simp
  have hsin: "sin (pi * t) = sin v" unfolding hpt by simp
  have hS: "0 \<le> sin v" by (rule sin_ge_zero[OF v0 vpi])
  note hP = P_nonneg[OF v0 vpi]
  have hsq: "(sin (v/2))\<^sup>2 = (1 - cos v) / 2"
    using cos_double_sin[of "v/2"] by simp
  define C where "C = (1 + cos v) / 2"
  define S where "S = sin v / pi"
  have hC1: "0 \<le> 1 - C" unfolding C_def using cos_le_one[of v] by simp
  have hS0: "0 \<le> S" unfolding S_def using hS pp by simp
  have hY: "0 \<le> t - C + t * S"
  proof -
    have e: "pi\<^sup>2 * (t - C + t * S) = pi\<^sup>2 * (sin (v/2))\<^sup>2 - pi * v + (pi - v) * sin v"
    proof -
      have s1: "pi * S = sin v" unfolding S_def using pne by simp
      have "pi\<^sup>2 * (t - C + t * S) = pi * (pi * t) - pi\<^sup>2 * C + (pi * t) * (pi * S)"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> = pi * (pi - v) - pi\<^sup>2 * C + (pi - v) * sin v"
        unfolding hpt s1 ..
      also have "\<dots> = pi\<^sup>2 * (sin (v/2))\<^sup>2 - pi * v + (pi - v) * sin v"
        unfolding hsq C_def by (simp add: power2_eq_square field_simps)
      finally show ?thesis .
    qed
    have h2: "0 \<le> pi\<^sup>2 * (t - C + t * S)" using e hP by simp
    show ?thesis using h2 pp by (simp add: zero_le_mult_iff)
  qed
  have hD: "0 < t + a * (1 - t)"
  proof -
    have "0 \<le> t * (1 - a)" using t0 a1 by (intro mult_nonneg_nonneg) auto
    thus ?thesis using a0 by (simp add: algebra_simps)
  qed
  have hHM: "t \<le> t powr a * (t + a * (1 - t))"
  proof (cases "t = 0")
    case True
    thus ?thesis by simp
  next
    case False
    thus ?thesis using rpow_hm[of t a] t0 a0 a1 by simp
  qed
  have hF: "0 \<le> t - (t + a * (1 - t)) * (C - a * S)"
  proof -
    have e: "t - (t + a * (1 - t)) * (C - a * S)
        = (1 - a) * (t * (1 - C)) + a * (t - C + t * S) + a\<^sup>2 * ((1 - t) * S)"
      by (simp add: power2_eq_square algebra_simps)
    have h1: "0 \<le> (1 - a) * (t * (1 - C))"
      using a1 t0 hC1 by (intro mult_nonneg_nonneg) auto
    have h2: "0 \<le> a * (t - C + t * S)" using a0 hY by (intro mult_nonneg_nonneg) auto
    have h3: "0 \<le> a\<^sup>2 * ((1 - t) * S)" using t1 hS0 by (intro mult_nonneg_nonneg) auto
    show ?thesis unfolding e using h1 h2 h3 by simp
  qed
  have hG: "0 \<le> (t powr a - (C - a * S)) * (t + a * (1 - t))"
  proof -
    have "(t powr a - (C - a * S)) * (t + a * (1 - t))
       = t powr a * (t + a * (1 - t)) - (t + a * (1 - t)) * (C - a * S)"
      by (simp add: algebra_simps)
    thus ?thesis using hHM hF by linarith
  qed
  have hGnn: "0 \<le> t powr a - (C - a * S)"
  proof (rule ccontr)
    assume "\<not> 0 \<le> t powr a - (C - a * S)"
    hence "t powr a - (C - a * S) < 0" by simp
    hence "(t powr a - (C - a * S)) * (t + a * (1 - t)) < 0" using hD by (rule mult_neg_pos)
    thus False using hG by simp
  qed
  have e: "t powr a - (1 - - cos v) / 2 + a / pi * sin v = t powr a - (C - a * S)"
    unfolding C_def S_def by (simp add: field_simps)
  show ?thesis unfolding hcos hsin using hGnn e by simp
qed

lemma ge_alg:
  fixes a X Z S T c :: real
  assumes a0: "0 \<le> a" and a1: "a \<le> 1" and hq: "1 + a * (1 - Z) \<le> T"
    and hx: "X \<le> 1/2 - c / 2" and hB: "-X \<le> 1 - Z - S" and hX: "0 \<le> X"
  shows "0 \<le> T - 1/2 - c / 2 - a * S"
proof -
  have h1: "-(a * X) \<le> a - a * Z - a * S"
    using mult_left_mono[OF hB a0] by (simp add: algebra_simps)
  have h2: "a * X \<le> X" using mult_right_mono[OF a1 hX] by simp
  have hq': "1 + a - a * Z \<le> T" using hq by (simp add: algebra_simps)
  show ?thesis using hq' hx h1 h2 by linarith
qed

lemma zz_aux_ge:
  assumes a0: "0 < a" and a1: "a \<le> 1" and t1: "1 \<le> t"
  shows "0 \<le> t powr a - (1 - cos (pi * t)) / 2 + a / pi * sin (pi * t)"
proof -
  have pp: "0 < pi" by simp
  have p3: "3 < pi" using pi_gt3 .
  have t0: "0 < t" using t1 by simp
  have hq: "1 + a * (1 - 1/t) \<le> t powr a"
  proof -
    have e1: "t powr a = exp (a * ln t)" using t0 by (simp add: powr_def)
    have h1: "1 + a * ln t \<le> exp (a * ln t)" by (rule exp_ge_add_one_self)
    have h2: "1 - 1/t \<le> ln t"
    proof -
      have "ln (1/t) \<le> 1/t - 1" using t0 by (intro ln_le_minus_one) simp
      moreover have "ln (1/t) = - ln t" using t0 by (simp add: ln_div)
      ultimately show ?thesis by linarith
    qed
    have h3: "a * (1 - 1/t) \<le> a * ln t" by (rule mult_left_mono[OF h2]) (use a0 in simp)
    show ?thesis using e1 h1 h3 by linarith
  qed
  obtain u where ud: "u = pi * (t - 1)" by blast
  have u0: "0 \<le> u" unfolding ud by (rule mult_nonneg_nonneg) (use pp t1 in auto)
  have hpt: "pi * t = u + pi" using ud by (simp add: algebra_simps)
  have hcos: "cos (pi * t) = - cos u" unfolding hpt by (simp add: cos_add)
  have hsin: "sin (pi * t) = - sin u" unfolding hpt by (simp add: sin_add)
  have eS: "a / pi * - sin u = - (a * (sin u / pi))" by (simp add: field_simps)
  have key: "0 \<le> t powr a - (1 - - cos u) / 2 + a / pi * - sin u"
  proof (cases "u \<le> pi")
    case True
    have hz: "0 \<le> t - 1" using t1 by simp
    have hs1: "t - 1 \<le> sin (u/2)"
    proof -
      have "2 / pi * (u/2) \<le> sin (u/2)" by (rule jordan) (use u0 True in auto)
      moreover have "2 / pi * (u/2) = t - 1" unfolding ud using pp by simp
      ultimately show ?thesis by simp
    qed
    have hs2: "(t - 1)\<^sup>2 \<le> (sin (u/2))\<^sup>2" by (rule power_mono[OF hs1 hz])
    have hsq: "(sin (u/2))\<^sup>2 = 1/2 - cos u / 2"
    proof -
      have h' : "cos u = 1 - 2 * (sin (u/2))\<^sup>2" using cos_double_sin[of "u/2"] by simp
      show ?thesis using h' by linarith
    qed
    have hsl: "sin u / pi \<le> t - 1"
    proof -
      have "sin u \<le> u" by (rule sin_x_le_x[OF u0])
      hence "sin u \<le> (t - 1) * pi" unfolding ud by (simp add: algebra_simps)
      thus ?thesis using pp by (simp add: pos_divide_le_eq)
    qed
    have hinv2: "1 / t \<le> t\<^sup>2 - 3 * t + 3"
    proof -
      have c3: "0 \<le> (t - 1) ^ 3" using hz by simp
      have "1 \<le> (t\<^sup>2 - 3 * t + 3) * t"
        using c3 by (simp add: power3_eq_cube power2_eq_square algebra_simps)
      thus ?thesis using t0 by (simp add: divide_le_eq)
    qed
    have e13: "(t - 1)\<^sup>2 = t\<^sup>2 - 2 * t + 1" by (simp add: power2_eq_square algebra_simps)
    have hB: "-(t - 1)\<^sup>2 \<le> 1 - 1/t - sin u / pi"
      using hsl hinv2 e13 by linarith
    have hx: "(t - 1)\<^sup>2 \<le> 1/2 - cos u / 2" using hs2 hsq by linarith
    have hX: "0 \<le> (t - 1)\<^sup>2" by simp
    note g = ge_alg[OF less_imp_le[OF a0] a1 hq hx hB hX]
    have e5: "t powr a - (1 - - cos u) / 2 + a / pi * - sin u
        = t powr a - 1/2 - cos u / 2 - a * (sin u / pi)" by (simp add: field_simps)
    show ?thesis unfolding e5 by (rule g)
  next
    case False
    hence upi: "pi \<le> u" by simp
    have ht2: "2 \<le> t"
    proof (rule ccontr)
      assume "\<not> 2 \<le> t"
      hence "t < 2" by simp
      hence "pi * (t - 1) < pi * 1" using pp by (intro mult_strict_left_mono) auto
      thus False using upi ud by simp
    qed
    have hinv2: "1 / t \<le> 1 / 2" using ht2 by (intro divide_left_mono) auto
    have hsl: "sin u / pi \<le> 1 / 3"
    proof -
      have "sin u \<le> 1" by simp
      hence "sin u / pi \<le> 1 / pi" using pp by (intro divide_right_mono) auto
      moreover have "1 / pi \<le> 1 / 3" using p3 by (intro divide_left_mono) auto
      ultimately show ?thesis by linarith
    qed
    have hB: "0 \<le> 1 - 1/t - sin u / pi" using hinv2 hsl by linarith
    have hx0: "(0::real) \<le> 1/2 - cos u / 2" using cos_le_one[of u] by linarith
    have hB0: "-(0::real) \<le> 1 - 1/t - sin u / pi" using hB by simp
    note g = ge_alg[OF less_imp_le[OF a0] a1 hq hx0 hB0 order_refl]
    have e5: "t powr a - (1 - - cos u) / 2 + a / pi * - sin u
        = t powr a - 1/2 - cos u / 2 - a * (sin u / pi)" by (simp add: field_simps)
    show ?thesis unfolding e5 by (rule g)
  qed
  show ?thesis unfolding hcos hsin using key by simp
qed

lemma zz_aux:
  assumes "0 < a" "a \<le> 1" "0 \<le> t"
  shows "0 \<le> t powr a - (1 - cos (pi * t)) / 2 + a / pi * sin (pi * t)"
  using assms zz_aux_le zz_aux_ge by (cases "t \<le> 1") auto

section \<open>The Zielinski--Zych inequality and speed limit\<close>

text \<open>The first theorem is the analytic core: a pointwise inequality between the power function and a cosine--sine combination. The second theorem turns it into the speed limit: if the survival amplitude of a state with energy distribution p vanishes at time ta, then ta is bounded below in terms of the fractional energy moment M of order a.\<close>

theorem zz_inequality:
  assumes a0: "0 < a" and a1: "a \<le> 1" and x0: "0 \<le> x"
  shows "0 \<le> x powr a - pi powr a / 2 + pi powr a / 2 * cos x + a * pi powr (a - 1) * sin x"
proof -
  have pp: "0 < pi" by simp
  obtain t where t0: "0 \<le> t" and xt: "x = pi * t"
    by (rule that[of "x / pi"]) (use x0 pp in \<open>auto simp: field_simps\<close>)
  note hG = zz_aux[OF a0 a1 t0]
  have e1: "(pi * t) powr a = pi powr a * t powr a" by (rule powr_mult)
  have e2: "pi powr (a - 1) = pi powr a / pi" using pp by (simp add: powr_diff powr_one)
  have h: "0 \<le> pi powr a * (t powr a - (1 - cos (pi * t)) / 2 + a / pi * sin (pi * t))"
    using hG by simp
  have e3: "pi powr a * (t powr a - (1 - cos (pi * t)) / 2 + a / pi * sin (pi * t))
      = pi powr a * t powr a - pi powr a / 2 + pi powr a / 2 * cos (pi * t)
        + a * (pi powr a / pi) * sin (pi * t)"
    by (simp add: field_simps)
  show ?thesis unfolding xt e1 e2 using h e3 by linarith
qed

theorem zielinski_zych:
  fixes p E :: "nat \<Rightarrow> real" and e0 a M ta :: real
  assumes a0: "0 < a" and a1: "a \<le> 1"
    and hp: "\<forall>n. 0 \<le> p n" and hE: "\<forall>n. e0 \<le> E n" and hta: "0 \<le> ta"
    and hsum: "p sums 1"
    and hM: "(\<lambda>n. p n * (E n - e0) powr a) sums M"
    and hRe: "(\<lambda>n. p n * cos (E n * ta)) sums 0"
    and hIm: "(\<lambda>n. p n * sin (E n * ta)) sums 0"
  shows "pi powr a \<le> 2 * M * ta powr a"
proof -
  have hc: "(\<lambda>n. p n * cos (E n * ta - e0 * ta)) sums 0"
  proof -
    note h = sums_add[OF sums_mult[OF hRe, of "cos (e0 * ta)"] sums_mult[OF hIm, of "sin (e0 * ta)"]]
    have eq: "(\<lambda>n. p n * cos (E n * ta - e0 * ta))
        = (\<lambda>n. cos (e0 * ta) * (p n * cos (E n * ta)) + sin (e0 * ta) * (p n * sin (E n * ta)))"
      by (rule ext) (simp add: cos_diff algebra_simps)
    show ?thesis unfolding eq using h by simp
  qed
  have hs: "(\<lambda>n. p n * sin (E n * ta - e0 * ta)) sums 0"
  proof -
    note h = sums_diff[OF sums_mult[OF hIm, of "cos (e0 * ta)"] sums_mult[OF hRe, of "sin (e0 * ta)"]]
    have eq: "(\<lambda>n. p n * sin (E n * ta - e0 * ta))
        = (\<lambda>n. cos (e0 * ta) * (p n * sin (E n * ta)) - sin (e0 * ta) * (p n * cos (E n * ta)))"
      by (rule ext) (simp add: sin_diff algebra_simps)
    show ?thesis unfolding eq using h by simp
  qed
  note hT = sums_add[OF sums_diff[OF sums_mult[OF hM, of "ta powr a"] sums_mult[OF hsum, of "pi powr a / 2"]]
     sums_mult[OF hc, of "pi powr a / 2"]]
  note hT2 = sums_add[OF hT sums_mult[OF hs, of "a * pi powr (a - 1)"]]
  have hterm: "\<And>n. 0 \<le> (ta powr a * (p n * (E n - e0) powr a) - pi powr a / 2 * p n)
      + pi powr a / 2 * (p n * cos (E n * ta - e0 * ta))
      + a * pi powr (a - 1) * (p n * sin (E n * ta - e0 * ta))"
  proof -
    fix n
    have dn: "0 \<le> E n - e0" using hE by simp
    have hpn: "0 \<le> p n" using hp by simp
    note h = zz_inequality[OF a0 a1 mult_nonneg_nonneg[OF hta dn]]
    have e: "(ta * (E n - e0)) powr a = ta powr a * (E n - e0) powr a" by (rule powr_mult)
    have c1: "cos (ta * (E n - e0)) = cos (E n * ta - e0 * ta)" by (simp add: algebra_simps)
    have c2: "sin (ta * (E n - e0)) = sin (E n * ta - e0 * ta)" by (simp add: algebra_simps)
    note h2 = h[unfolded e c1 c2]
    note hm = mult_nonneg_nonneg[OF hpn h2]
    have eqG: "(ta powr a * (p n * (E n - e0) powr a) - pi powr a / 2 * p n)
      + pi powr a / 2 * (p n * cos (E n * ta - e0 * ta))
      + a * pi powr (a - 1) * (p n * sin (E n * ta - e0 * ta))
      = p n * (ta powr a * (E n - e0) powr a - pi powr a / 2 + pi powr a / 2 * cos (E n * ta - e0 * ta)
        + a * pi powr (a - 1) * sin (E n * ta - e0 * ta))"
      by (simp add: algebra_simps)
    show "0 \<le> (ta powr a * (p n * (E n - e0) powr a) - pi powr a / 2 * p n)
      + pi powr a / 2 * (p n * cos (E n * ta - e0 * ta))
      + a * pi powr (a - 1) * (p n * sin (E n * ta - e0 * ta))"
      unfolding eqG by (rule hm)
  qed
  have hnn: "0 \<le> ta powr a * M - pi powr a / 2 * 1 + pi powr a / 2 * 0 + a * pi powr (a - 1) * 0"
    by (rule sums_le[OF hterm sums_zero hT2])
  show ?thesis using hnn by (simp add: algebra_simps)
qed

section \<open>The limit a -> 0\<close>

text \<open>As the exponent tends to 0 the fractional moment tends to the weight of the excited levels, 1 - p 0; hence the bound tends to infinity when p 0 > 1/2 and to 0 when p 0 < 1/2.\<close>

theorem tendsto_fractional_moment:
  fixes p E :: "nat \<Rightarrow> real" and e0 a0 :: real
  assumes hp: "\<forall>n. 0 \<le> p n" and hsum: "p sums 1"
    and h0: "E 0 = e0" and hE: "\<forall>n. n \<noteq> 0 \<longrightarrow> e0 < E n"
    and ha0: "0 < a0" and hmom: "summable (\<lambda>n. p n * (E n - e0) powr a0)"
  shows "((\<lambda>a. (\<Sum>n. p n * (E n - e0) powr a)) \<longlongrightarrow> 1 - p 0) (at_right 0)"
proof -
  let ?a = "\<lambda>k (a::real). p k * (E k - e0) powr a"
  let ?b = "\<lambda>k. if k = 0 then 0 else p k"
  let ?M = "\<lambda>k. p k * (1 + (E k - e0) powr a0)"
  have hE': "\<And>n. 0 \<le> E n - e0"
  proof -
    fix n
    show "0 \<le> E n - e0" using hE h0 by (cases "n = 0") (auto simp: less_imp_le)
  qed
  have hMs: "summable ?M"
  proof -
    have "summable (\<lambda>n. p n + p n * (E n - e0) powr a0)" using sums_summable[OF hsum] hmom by (rule summable_add)
    moreover have "(\<lambda>n. p n + p n * (E n - e0) powr a0) = ?M" by (rule ext) (simp add: algebra_simps)
    ultimately show ?thesis by simp
  qed
  have lim: "\<And>k. ((\<lambda>a. ?a k a) \<longlongrightarrow> ?b k) (at_right 0)"
  proof -
    fix k
    show "((\<lambda>a. ?a k a) \<longlongrightarrow> ?b k) (at_right 0)"
    proof (cases "k = 0")
      case True
      thus ?thesis by (simp add: h0)
    next
      case False
      have ek: "e0 < E k" using hE False by blast
      have cpos: "E k - e0 \<noteq> 0" using ek by (intro notI) linarith
      have hid: "((\<lambda>x::real. x) \<longlongrightarrow> 0) (at_right 0)"
        unfolding at_right_eq by (rule tendsto_ident_at)
      have "((\<lambda>a. (E k - e0) powr a) \<longlongrightarrow> (E k - e0) powr 0) (at_right 0)"
        by (rule tendsto_powr[OF tendsto_const hid cpos])
      hence "((\<lambda>a. p k * (E k - e0) powr a) \<longlongrightarrow> p k * (E k - e0) powr 0) (at_right 0)"
        by (rule tendsto_mult[OF tendsto_const])
      thus ?thesis using False cpos by simp
    qed
  qed
  have ev: "\<forall>\<^sub>F a in at_right (0::real). 0 < a \<and> a < a0"
  proof (subst eventually_at_right[OF ha0])
    show "\<exists>b>0. \<forall>y>0. y < b \<longrightarrow> 0 < y \<and> y < a0" using ha0 by (intro exI[of _ a0]) auto
  qed
  have bound: "eventually (\<lambda>(k,a). norm (?a k a) \<le> ?M k) (at_top \<times>\<^sub>F at_right 0)"
  proof -
    have "\<And>k a. 0 < a \<and> a < a0 \<Longrightarrow> norm (?a k a) \<le> ?M k"
    proof -
      fix k and a :: real
      assume ha: "0 < a \<and> a < a0"
      have c0: "0 \<le> E k - e0" by (rule hE')
      have pk: "0 \<le> p k" using hp by simp
      have n: "norm (?a k a) = p k * (E k - e0) powr a" using pk by simp
      have ineq: "(E k - e0) powr a \<le> 1 + (E k - e0) powr a0"
      proof (cases "1 \<le> E k - e0")
        case True
        have "(E k - e0) powr a \<le> (E k - e0) powr a0" using True ha by (intro powr_mono) auto
        thus ?thesis by linarith
      next
        case False
        have "(E k - e0) powr a \<le> 1" using False c0 ha by (intro powr_le1) auto
        thus ?thesis using powr_ge_zero[of "E k - e0" a0] by linarith
      qed
      show "norm (?a k a) \<le> ?M k" unfolding n using ineq pk by (intro mult_left_mono) auto
    qed
    thus ?thesis unfolding eventually_prod_filter
      by (intro exI[of _ "\<lambda>_::nat. True"] exI[of _ "\<lambda>a::real. 0 < a \<and> a < a0"]) (auto intro: ev)
  qed
  have nb: "at_right (0::real) \<noteq> bot" by simp
  note T = tannerys_theorem[OF lim bound hMs nb]
  have sbn: "summable (\<lambda>n. norm (?b n))" using T by blast
  have T3: "((\<lambda>a. \<Sum>k. ?a k a) \<longlongrightarrow> (\<Sum>k. ?b k)) (at_right 0)" using T by blast
  have sb: "summable ?b" by (rule summable_norm_cancel[OF sbn])
  have sp: "summable p" by (rule sums_summable[OF hsum])
  have s1: "(\<Sum>n. ?b (Suc n)) = suminf ?b - ?b 0" by (rule suminf_split_head[OF sb])
  have s2: "(\<Sum>n. p (Suc n)) = suminf p - p 0" by (rule suminf_split_head[OF sp])
  have s3: "suminf p = 1" by (rule sums_unique[OF hsum, symmetric])
  have s4: "(\<Sum>n. ?b (Suc n)) = (\<Sum>n. p (Suc n))" by simp
  have eqb: "(\<Sum>k. ?b k) = 1 - p 0" using s1 s2 s3 s4 by simp
  show ?thesis using T3 eqb by simp
qed

section \<open>Behaviour of the bound as a -> 0\<close>

lemma bound_eq:
  fixes M :: "real \<Rightarrow> real"
  shows "\<forall>\<^sub>F a in at_right (0::real). 0 < M a \<longrightarrow>
     pi / (2 * M a) powr (1 / a) = pi * exp (- (ln (2 * M a) * inverse a))"
proof (rule always_eventually, rule allI, rule impI)
  fix a :: real
  assume ha: "0 < M a"
  have h2: "2 * M a \<noteq> 0" using ha by simp
  have e1: "(2 * M a) powr (1 / a) = exp (ln (2 * M a) * inverse a)"
    using h2 by (simp add: powr_def inverse_eq_divide mult.commute)
  show "pi / (2 * M a) powr (1 / a) = pi * exp (- (ln (2 * M a) * inverse a))"
    unfolding e1 by (simp add: exp_minus divide_inverse)
qed

lemma bound_at_top:
  fixes M :: "real \<Rightarrow> real" and c :: real
  assumes hM: "(M \<longlongrightarrow> c) (at_right 0)" and hc0: "0 < c" and hc1: "2 * c < 1"
  shows "LIM a at_right 0. pi / (2 * M a) powr (1 / a) :> at_top"
proof -
  have h2M: "((\<lambda>a. 2 * M a) \<longlongrightarrow> 2 * c) (at_right 0)"
    by (rule tendsto_mult[OF tendsto_const hM])
  have hlog: "((\<lambda>a. ln (2 * M a)) \<longlongrightarrow> ln (2 * c)) (at_right 0)"
    by (rule tendsto_ln[OF h2M]) (use hc0 in simp)
  have hneg: "ln (2 * c) < 0" by (rule ln_less_zero) (use hc0 hc1 in auto)
  have hinv: "LIM a at_right (0::real). inverse a :> at_top" by (rule filterlim_inverse_at_top_right)
  have hprod: "LIM a at_right 0. ln (2 * M a) * inverse a :> at_bot"
    by (rule filterlim_tendsto_neg_mult_at_bot[OF hlog hneg hinv])
  note hneg' = iffD1[OF filterlim_uminus_at_bot hprod]
  have hexp: "LIM a at_right 0. exp (- (ln (2 * M a) * inverse a)) :> at_top"
    by (rule filterlim_compose[OF exp_at_top hneg'])
  have hfin: "LIM a at_right 0. pi * exp (- (ln (2 * M a) * inverse a)) :> at_top"
    by (rule filterlim_tendsto_pos_mult_at_top[OF tendsto_const pi_gt_zero hexp])
  have hMpos: "\<forall>\<^sub>F a in at_right (0::real). 0 < M a" by (rule order_tendstoD(1)[OF hM hc0])
  have ev: "\<forall>\<^sub>F a in at_right (0::real).
      pi / (2 * M a) powr (1 / a) = pi * exp (- (ln (2 * M a) * inverse a))"
    using hMpos bound_eq[of M] by (rule eventually_elim2) auto
  show ?thesis by (rule iffD2[OF filterlim_cong[OF refl refl ev] hfin])
qed

lemma bound_zero:
  fixes M :: "real \<Rightarrow> real" and c :: real
  assumes hM: "(M \<longlongrightarrow> c) (at_right 0)" and hc1: "1 < 2 * c"
  shows "((\<lambda>a. pi / (2 * M a) powr (1 / a)) \<longlongrightarrow> 0) (at_right 0)"
proof -
  have hc0: "0 < c" using hc1 by simp
  have h2M: "((\<lambda>a. 2 * M a) \<longlongrightarrow> 2 * c) (at_right 0)"
    by (rule tendsto_mult[OF tendsto_const hM])
  have hlog: "((\<lambda>a. ln (2 * M a)) \<longlongrightarrow> ln (2 * c)) (at_right 0)"
    by (rule tendsto_ln[OF h2M]) (use hc0 in simp)
  have hpos: "0 < ln (2 * c)" by (rule ln_gt_zero) (use hc1 in simp)
  have hinv: "LIM a at_right (0::real). inverse a :> at_top" by (rule filterlim_inverse_at_top_right)
  have hprod: "LIM a at_right 0. ln (2 * M a) * inverse a :> at_top"
    by (rule filterlim_tendsto_pos_mult_at_top[OF hlog hpos hinv])
  note hneg' = iffD1[OF filterlim_uminus_at_top hprod]
  have hexp: "((\<lambda>a. exp (- (ln (2 * M a) * inverse a))) \<longlongrightarrow> 0) (at_right 0)"
    by (rule filterlim_compose[OF exp_at_bot hneg'])
  have hfin: "((\<lambda>a. pi * exp (- (ln (2 * M a) * inverse a))) \<longlongrightarrow> pi * 0) (at_right 0)"
    by (rule tendsto_mult[OF tendsto_const hexp])
  have hMpos: "\<forall>\<^sub>F a in at_right (0::real). 0 < M a" by (rule order_tendstoD(1)[OF hM hc0])
  have ev: "\<forall>\<^sub>F a in at_right (0::real).
      pi / (2 * M a) powr (1 / a) = pi * exp (- (ln (2 * M a) * inverse a))"
    using hMpos bound_eq[of M] by (rule eventually_elim2) auto
  show ?thesis by (rule iffD2[OF tendsto_cong[OF ev]]) (use hfin in simp)
qed

theorem zz_bound_tendsto_at_top:
  fixes p E :: "nat \<Rightarrow> real" and e0 a0 :: real
  assumes hp: "\<forall>n. 0 \<le> p n" and hsum: "p sums 1"
    and h0: "E 0 = e0" and hE: "\<forall>n. n \<noteq> 0 \<longrightarrow> e0 < E n"
    and ha0: "0 < a0" and hmom: "summable (\<lambda>n. p n * (E n - e0) powr a0)"
    and hhalf: "1/2 < p 0" and hone: "p 0 < 1"
  shows "LIM a at_right 0. pi / (2 * (\<Sum>n. p n * (E n - e0) powr a)) powr (1 / a) :> at_top"
proof -
  have c0: "0 < 1 - p 0" using hone by simp
  have c1: "2 * (1 - p 0) < 1" using hhalf by simp
  show ?thesis by (rule bound_at_top[OF tendsto_fractional_moment[OF hp hsum h0 hE ha0 hmom] c0 c1])
qed

theorem zz_bound_tendsto_zero:
  fixes p E :: "nat \<Rightarrow> real" and e0 a0 :: real
  assumes hp: "\<forall>n. 0 \<le> p n" and hsum: "p sums 1"
    and h0: "E 0 = e0" and hE: "\<forall>n. n \<noteq> 0 \<longrightarrow> e0 < E n"
    and ha0: "0 < a0" and hmom: "summable (\<lambda>n. p n * (E n - e0) powr a0)"
    and hhalf: "p 0 < 1/2"
  shows "((\<lambda>a. pi / (2 * (\<Sum>n. p n * (E n - e0) powr a)) powr (1 / a)) \<longlongrightarrow> 0) (at_right 0)"
proof -
  have c1: "1 < 2 * (1 - p 0)" using hhalf by simp
  show ?thesis by (rule bound_zero[OF tendsto_fractional_moment[OF hp hsum h0 hE ha0 hmom] c1])
qed

end
