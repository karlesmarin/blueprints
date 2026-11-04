(*  Title:      Relay_Ramp_Time.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Minimal transfer time of the qubit--bus--qubit relay with a time-dependent coupling envelope, and
    the closed form for ramped couplings: triangular or trapezoidal envelope.
*)
theory Relay_Ramp_Time
  imports Relay_Extensions Relay_Minimal_Time
begin

text \<open>In the theory of the minimal transfer time the couplings are bounded by a constant G, and the
conclusion is pi / sqrt 2 <= G T. Here the bound is a time-dependent envelope m(t): the derivatives of
the moduli of the amplitudes of the two qubits are bounded by m(t) times the square root of the bus
occupation, and the conclusion is pi / sqrt 2 <= the integral of m over [0, T]. The proof is the one
for constant G, with the primitive M(t) = integral of m over [0, t] in place of G t. For ramped couplings
the envelope is the trapezoid of the theory on weighted forms of the loss floor, its integral is computed, and inverting this integral
gives the minimal time: 2 sqrt (A / S) when the envelope is triangular, A / G + G / S when it is
trapezoidal, where A = pi / sqrt 2.\<close>

section \<open>The key derivative with a variable primitive\<close>

text \<open>The same as the key derivative lemma of the minimal time theory, with the function G t replaced by a
function M whose derivative at the point is G. The proof is the one of that lemma, with this hypothesis in place of the derivative of G t.\<close>


lemma key_deriv_var:
  fixes x z M :: "real \<Rightarrow> real" and G x1 z1 :: real
  assumes G: "0 \<le> G" and hM: "(M has_real_derivative G) (at t)"
    and hx: "(x has_real_derivative x1) (at t)" and hz: "(z has_real_derivative z1) (at t)"
    and x0: "0 \<le> x t" and z0: "0 \<le> z t" and D: "(x t)^2 + (z t)^2 \<le> 1" and xn: "x t \<noteq> 1" and zn: "z t \<noteq> 1"
    and bx: "\<bar>x1\<bar> \<le> G * sqrt (1 - (x t)^2 - (z t)^2)" and bz: "\<bar>z1\<bar> \<le> G * sqrt (1 - (x t)^2 - (z t)^2)"
    and hs: "x t + z t = 1 \<Longrightarrow> x1 + z1 = 0"
  shows "\<exists>c. 0 \<le> c \<and> ((\<lambda>u. M u + Phi (x u) (z u)) has_real_derivative c) (at t)"
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
    have X1: "((\<lambda>u. M u + arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2) has_real_derivative
        G + (((x1 - z1) + (x t - z t) * (x t + z t) * (x1 + z1) / (2 - (x t + z t)^2)) / (2 * y))) (at t)"
      by (rule DERIV_add[OF hM dv])
    have "((\<lambda>u. M u + Phi (x u) (z u)) has_real_derivative
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
    have X2: "((\<lambda>u. M u + arcsin (x u - z u) / sqrt 2) has_real_derivative
        G + (x1 - z1) / (sqrt 2 * sqrt (1 - (x t - z t)^2))) (at t)" by (rule DERIV_add[OF hM dv])
    have "((\<lambda>u. M u + Phi (x u) (z u)) has_real_derivative
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
    have f12: "M t + arcsin ((x t - z t) / sqrt (2 - (x t + z t)^2)) / sqrt 2 = M t + arcsin (x t - z t) / sqrt 2"
      using 2 by simp
    have "((\<lambda>u. M u + Phi (x u) (z u)) has_real_derivative G + (x1 - z1) / (2 * y)) (at t)"
    proof (rule squeeze_deriv[where fa = "\<lambda>u. M u + arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2"
        and fb = "\<lambda>u. M u + arcsin (x u - z u) / sqrt 2"])
      show "((\<lambda>u. M u + arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2) has_real_derivative
          G + (x1 - z1) / (2 * y)) (at t)" by (rule DERIV_add[OF hM dv1])
      show "((\<lambda>u. M u + arcsin (x u - z u) / sqrt 2) has_real_derivative
          G + (x1 - z1) / (2 * y)) (at t)" by (rule DERIV_add[OF hM dv2])
      show "M t + arcsin ((x t - z t) / sqrt (2 - (x t + z t)^2)) / sqrt 2 = M t + arcsin (x t - z t) / sqrt 2"
        by (rule f12)
      show "M t + Phi (x t) (z t) = M t + arcsin ((x t - z t) / sqrt (2 - (x t + z t)^2)) / sqrt 2"
        using 2 by (simp add: Phi_def)
      show "\<And>u. M u + Phi (x u) (z u) = M u + arcsin ((x u - z u) / sqrt (2 - (x u + z u)^2)) / sqrt 2
          \<or> M u + Phi (x u) (z u) = M u + arcsin (x u - z u) / sqrt 2"
        by (simp add: Phi_def)
    qed
    moreover have "0 \<le> G + (x1 - z1) / (2 * y)" by (rule nn_from_abs[OF bd])
    ultimately show ?thesis by blast
  qed
qed

section \<open>The theorem with an envelope\<close>

text \<open>Hypotheses as in the minimal time theorem, except that the bounds on the derivatives of x and z carry a
continuous non-negative envelope m(t) in place of the constant G. Conclusion: pi / sqrt 2 <= the integral of
m over [0, T].\<close>


theorem relay_minimal_time_var:
  fixes x z x' z' m :: "real \<Rightarrow> real" and T :: real and S :: "real set"
  assumes T: "0 \<le> T" and S: "countable S"
    and cx: "continuous_on {0..T} x" and cz: "continuous_on {0..T} z"
    and D: "\<forall>t\<in>{0..T}. 0 \<le> x t \<and> 0 \<le> z t \<and> (x t)^2 + (z t)^2 \<le> 1"
    and x0: "x 0 = 1" and zT: "z T = 1"
    and der: "\<forall>t\<in>{0<..<T} - S. (x has_real_derivative x' t) (at t) \<and> (z has_real_derivative z' t) (at t)"
    and mc: "continuous_on {0..T} m" and m0: "\<forall>t\<in>{0..T}. 0 \<le> m t"
    and bnd: "\<forall>t\<in>{0<..<T} - S. \<bar>x' t\<bar> \<le> m t * sqrt (1 - (x t)^2 - (z t)^2) \<and> \<bar>z' t\<bar> \<le> m t * sqrt (1 - (x t)^2 - (z t)^2)"
  shows "pi / sqrt 2 \<le> integral {0..T} m"
proof -
  define M where "M = (\<lambda>u. integral {0..u} m)"
  have mint: "m integrable_on {0..T}" by (rule integrable_continuous_real[OF mc])
  have Mc: "continuous_on {0..T} M" unfolding M_def by (rule indefinite_integral_continuous_1[OF mint])
  have Mder: "\<And>u. u \<in> {0<..<T} \<Longrightarrow> (M has_real_derivative m u) (at u)"
  proof -
    fix u assume u: "u \<in> {0<..<T}"
    have w: "(M has_real_derivative m u) (at u within {0..T})"
      unfolding M_def by (rule integral_has_real_derivative[OF mc]) (use u in auto)
    have "at u within {0..T} = at u" by (rule at_within_interior) (use u in simp)
    thus "(M has_real_derivative m u) (at u)" using w by simp
  qed
  have Mnn: "\<And>u. u \<in> {0..T} \<Longrightarrow> 0 \<le> M u"
  proof -
    fix u assume u: "u \<in> {0..T}"
    have sub: "{0..u} \<subseteq> {0..T}" using u by auto
    show "0 \<le> M u" unfolding M_def
    proof (rule integral_nonneg)
      show "m integrable_on {0..u}" by (rule integrable_continuous_real[OF continuous_on_subset[OF mc sub]])
      show "\<And>x. x \<in> {0..u} \<Longrightarrow> 0 \<le> m x" using m0 sub by blast
    qed
  qed
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
  define h where "h = (\<lambda>u. M u + Phi (x u) (z u))"
  have hcont: "continuous_on {t0..t1} h"
  proof -
    have sub: "{t0..t1} \<subseteq> {0..T}" using t0r t1r by auto
    have "continuous_on {t0..t1} (\<lambda>t. Phi (x t) (z t))"
      by (rule cont_Phi) (use sub continuous_on_subset[OF cx sub] continuous_on_subset[OF cz sub] Dt in auto)
    hence a1: "continuous_on {t0..t1} (\<lambda>t. Phi (x t) (z t))" .
    have a2: "continuous_on {t0..t1} M" by (rule continuous_on_subset[OF Mc sub])
    show ?thesis unfolding h_def by (rule continuous_on_add[OF a2 a1])
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
    have m0u: "0 \<le> m u" using m0 uD by blast
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
      by (rule key_deriv_var[OF m0u Mder[OF uT] hx hz _ _ _ inner_x[OF u1] inner_z[OF u1] _ _ hs])
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
  have "pi / sqrt 2 \<le> M t1 - M t0"
  proof -
    have "0 \<le> (M t1 + (- ((pi / 2) / sqrt 2))) - (M t0 + (pi / 2) / sqrt 2)"
      using hnn unfolding h_def P0 P1 .
    hence "2 * ((pi / 2) / sqrt 2) \<le> M t1 - M t0" by linarith
    thus ?thesis unfolding pis_eq[symmetric] .
  qed
  also have "M t1 - M t0 \<le> integral {0..T} m"
  proof -
    have t1T: "t1 \<in> {0..T}" using t1r by simp
    have M0: "0 \<le> M t0" by (rule Mnn) (use t0r t1r in auto)
    have comb: "integral {0..t1} m + integral {t1..T} m = integral {0..T} m"
      by (rule Henstock_Kurzweil_Integration.integral_combine[OF t1r(1) t1r(2) mint])
    have tail: "0 \<le> integral {t1..T} m"
    proof (rule integral_nonneg)
      show "m integrable_on {t1..T}"
        by (rule integrable_continuous_real[OF continuous_on_subset[OF mc]]) (use t1r in auto)
      show "\<And>x. x \<in> {t1..T} \<Longrightarrow> 0 \<le> m x" using m0 t1r by auto
    qed
    show ?thesis using comb tail M0 unfolding M_def by linarith
  qed
  finally show ?thesis .
qed


section \<open>Integral of the trapezoidal envelope\<close>

text \<open>The envelope integral I(T) = int m of the ramped coupling envelope (the trapezoid of the theory on weighted forms of the loss floor):
S T\<^latex>\<open>\textsuperscript{2}\<close>/4 when the envelope is triangular (S T <= 2 G), and G T - G\<^latex>\<open>\textsuperscript{2}\<close>/S
when it is trapezoidal.\<close>

definition ramp_I :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "ramp_I S G T = (if S * T \<le> 2 * G then S * T ^ 2 / 4 else G * T - G ^ 2 / S)"

lemma lin_int:
  fixes c a b :: real
  assumes "a \<le> b"
  shows "((\<lambda>t. c * t) has_integral c * b ^ 2 / 2 - c * a ^ 2 / 2) {a..b}"
proof -
  have "\<And>x. ((\<lambda>t. c * t ^ 2 / 2) has_real_derivative c * x) (at x)"
    by (auto intro!: derivative_eq_intros simp: power2_eq_square)
  thus ?thesis using ftc_real[OF assms, where F = "\<lambda>t. c * t ^ 2 / 2" and f = "\<lambda>t. c * t"] by simp
qed

lemma lin_int_rev:
  fixes c a b T :: real
  assumes "a \<le> b"
  shows "((\<lambda>t. c * (T - t)) has_integral c * (T - a) ^ 2 / 2 - c * (T - b) ^ 2 / 2) {a..b}"
proof -
  have "\<And>x. ((\<lambda>t. - (c * (T - t) ^ 2 / 2)) has_real_derivative c * (T - x)) (at x)"
    by (auto intro!: derivative_eq_intros simp: power2_eq_square field_simps algebra_simps)
  thus ?thesis using ftc_real[OF assms, where F = "\<lambda>t. - (c * (T - t) ^ 2 / 2)" and f = "\<lambda>t. c * (T - t)"] by simp
qed

lemma env1:
  assumes a: "S * t \<le> S * (T - t)" and b: "S * t \<le> G"
  shows "ramp_env S G T t = S * t"
  unfolding ramp_env_def by (simp only: min_absorb1[OF a] min_absorb1[OF b])

lemma env2:
  assumes a: "S * (T - t) \<le> S * t" and b: "S * (T - t) \<le> G"
  shows "ramp_env S G T t = S * (T - t)"
  unfolding ramp_env_def by (simp only: min_absorb2[OF a] min_absorb1[OF b])

lemma env3:
  assumes a: "G \<le> S * t" and b: "G \<le> S * (T - t)"
  shows "ramp_env S G T t = G"
proof -
  have c: "G \<le> min (S * t) (S * (T - t))" using a b by simp
  show ?thesis unfolding ramp_env_def by (simp only: min_absorb2[OF c])
qed

theorem ramp_env_integral:
  fixes S G T :: real
  assumes S: "0 < S" and G: "0 < G" and T: "0 < T"
  shows "((\<lambda>t. ramp_env S G T t) has_integral ramp_I S G T) {0..T}"
proof (cases "S * T \<le> 2 * G")
  case True
  have p1: "((\<lambda>t. S * t) has_integral S * (T / 2) ^ 2 / 2) {0..T / 2}"
    using lin_int[where c = S and a = 0 and b = "T / 2"] T by simp
  have i1: "((\<lambda>t. ramp_env S G T t) has_integral S * (T / 2) ^ 2 / 2) {0..T / 2}"
  proof (rule has_integral_eq[OF _ p1])
    fix t assume t: "t \<in> {0..T / 2}"
    have a: "S * t \<le> S * (T - t)" using t S by (intro mult_left_mono) auto
    have b: "S * t \<le> G"
    proof -
      have "S * t \<le> S * (T / 2)" using t S by (intro mult_left_mono) auto
      moreover have "S * (T / 2) = S * T / 2" by simp
      ultimately show ?thesis using True by linarith
    qed
    show "S * t = ramp_env S G T t" by (rule env1[OF a b, symmetric])
  qed
  have p2: "((\<lambda>t. S * (T - t)) has_integral S * (T - T / 2) ^ 2 / 2) {T / 2..T}"
    using lin_int_rev[where c = S and T = T and a = "T / 2" and b = T] T by simp
  have i2: "((\<lambda>t. ramp_env S G T t) has_integral S * (T - T / 2) ^ 2 / 2) {T / 2..T}"
  proof (rule has_integral_eq[OF _ p2])
    fix t assume t: "t \<in> {T / 2..T}"
    have a: "S * (T - t) \<le> S * t" using t S by (intro mult_left_mono) auto
    have b: "S * (T - t) \<le> G"
    proof -
      have "S * (T - t) \<le> S * (T / 2)" using t S by (intro mult_left_mono) auto
      moreover have "S * (T / 2) = S * T / 2" by simp
      ultimately show ?thesis using True by linarith
    qed
    show "S * (T - t) = ramp_env S G T t" by (rule env2[OF a b, symmetric])
  qed
  have "((\<lambda>t. ramp_env S G T t) has_integral S * (T / 2) ^ 2 / 2 + S * (T - T / 2) ^ 2 / 2) {0..T}"
    by (rule has_integral_combine[OF _ _ i1 i2]) (use T in simp_all)
  moreover have "S * (T / 2) ^ 2 / 2 + S * (T - T / 2) ^ 2 / 2 = ramp_I S G T"
    unfolding ramp_I_def using True by (simp add: field_simps power2_eq_square)
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
  have p1: "((\<lambda>t. S * t) has_integral S * u ^ 2 / 2) {0..u}"
    using lin_int[where c = S and a = 0 and b = u] u0 by simp
  have i1: "((\<lambda>t. ramp_env S G T t) has_integral S * u ^ 2 / 2) {0..u}"
  proof (rule has_integral_eq[OF _ p1])
    fix t assume t: "t \<in> {0..u}"
    have a: "S * t \<le> S * (T - t)" using t S uT by (intro mult_left_mono) auto
    have b: "S * t \<le> G"
    proof -
      have "S * t \<le> S * u" using t S by (intro mult_left_mono) auto
      thus ?thesis using Su by simp
    qed
    show "S * t = ramp_env S G T t" by (rule env1[OF a b, symmetric])
  qed
  have uu: "u \<le> T - u" using uT by simp
  have p2: "((\<lambda>t. G) has_integral G * (T - u - u)) {u..T - u}"
  proof -
    have "((\<lambda>t. G) has_integral G * (T - u) - G * u) {u..T - u}"
      by (rule ftc_real[OF uu, where F = "\<lambda>t. G * t"]) (auto intro!: derivative_eq_intros)
    thus ?thesis by (simp add: algebra_simps)
  qed
  have i2: "((\<lambda>t. ramp_env S G T t) has_integral G * (T - u - u)) {u..T - u}"
  proof (rule has_integral_eq[OF _ p2])
    fix t assume t: "t \<in> {u..T - u}"
    have "S * u \<le> S * t" using t S by (intro mult_left_mono) auto
    hence a: "G \<le> S * t" using Su by simp
    have "S * u \<le> S * (T - t)" using t S by (intro mult_left_mono) auto
    hence b: "G \<le> S * (T - t)" using Su by simp
    show "G = ramp_env S G T t" by (rule env3[OF a b, symmetric])
  qed
  have p3: "((\<lambda>t. S * (T - t)) has_integral S * (T - (T - u)) ^ 2 / 2) {T - u..T}"
    using lin_int_rev[where c = S and T = T and a = "T - u" and b = T] u0 by simp
  have i3: "((\<lambda>t. ramp_env S G T t) has_integral S * (T - (T - u)) ^ 2 / 2) {T - u..T}"
  proof (rule has_integral_eq[OF _ p3])
    fix t assume t: "t \<in> {T - u..T}"
    have a: "S * (T - t) \<le> S * t" using t S uT by (intro mult_left_mono) auto
    have b: "S * (T - t) \<le> G"
    proof -
      have "S * (T - t) \<le> S * u" using t S by (intro mult_left_mono) auto
      thus ?thesis using Su by simp
    qed
    show "S * (T - t) = ramp_env S G T t" by (rule env2[OF a b, symmetric])
  qed
  have i12: "((\<lambda>t. ramp_env S G T t) has_integral S * u ^ 2 / 2 + G * (T - u - u)) {0..T - u}"
    by (rule has_integral_combine[OF _ _ i1 i2]) (use u0 uT in simp_all)
  have tot: "((\<lambda>t. ramp_env S G T t) has_integral
               S * u ^ 2 / 2 + G * (T - u - u) + S * (T - (T - u)) ^ 2 / 2) {0..T}"
    by (rule has_integral_combine[OF _ _ i12 i3]) (use u0 uT in simp_all)
  have "S * u ^ 2 / 2 + G * (T - u - u) + S * (T - (T - u)) ^ 2 / 2 = G * T - G ^ 2 / S"
    unfolding u_def using S by (simp add: field_simps power2_eq_square)
  thus ?thesis using tot False unfolding ramp_I_def by simp
qed

section \<open>Inverting the envelope integral: the minimal time\<close>

text \<open>With A = pi / sqrt 2, reparametrising time by the primitive of the envelope shows that the minimal time
for which the envelope integral reaches A is 2 sqrt (A / S) when S <= G\<^latex>\<open>\textsuperscript{2}\<close>/A
(triangular envelope) and A / G + G / S otherwise (trapezoidal envelope). Below, the first theorem says that
reaching A forces T to be at least this time, and its converse that it suffices.\<close>

definition ramp_Tmin :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "ramp_Tmin A S G = (if S \<le> G ^ 2 / A then 2 * sqrt (A / S) else A / G + G / S)"

lemma tri_time:
  fixes A S T :: real
  assumes A: "0 < A" and S: "0 < S" and T: "0 \<le> T" and hq: "A \<le> S * T ^ 2 / 4"
  shows "2 * sqrt (A / S) \<le> T"
proof -
  have a0: "0 \<le> A / S" using A S by simp
  have t2: "(2 * sqrt (A / S)) ^ 2 = 4 * (A / S)"
    by (simp only: power_mult_distrib real_sqrt_pow2[OF a0]) simp
  have e: "T ^ 2 * S = S * T ^ 2" by (rule mult.commute)
  have "4 * A \<le> T ^ 2 * S" using hq e by linarith
  hence "(4 * A) / S \<le> T ^ 2" by (simp only: pos_divide_le_eq[OF S])
  hence "(2 * sqrt (A / S)) ^ 2 \<le> T ^ 2" using t2 by simp
  thus ?thesis by (rule power2_le_imp_le[OF _ T])
qed

lemma tri_conv:
  fixes A S T :: real
  assumes A: "0 < A" and S: "0 < S" and T: "0 \<le> T" and hT: "2 * sqrt (A / S) \<le> T"
  shows "A \<le> S * T ^ 2 / 4"
proof -
  have a0: "0 \<le> A / S" using A S by simp
  have t2: "(2 * sqrt (A / S)) ^ 2 = 4 * (A / S)"
    by (simp only: power_mult_distrib real_sqrt_pow2[OF a0]) simp
  have "(2 * sqrt (A / S)) ^ 2 \<le> T ^ 2" by (rule power_mono[OF hT]) (use a0 in simp)
  hence "(4 * A) / S \<le> T ^ 2" using t2 by simp
  hence "4 * A \<le> T ^ 2 * S" by (simp only: pos_divide_le_eq[OF S])
  thus ?thesis using mult.commute[of "T ^ 2" S] by linarith
qed

theorem ramp_min_time:
  fixes A S G T :: real
  assumes A: "0 < A" and S: "0 < S" and G: "0 < G" and T: "0 < T"
    and hI: "A \<le> ramp_I S G T"
  shows "ramp_Tmin A S G \<le> T"
proof (cases "S \<le> G ^ 2 / A")
  case True
  have hAS: "S * A \<le> G ^ 2" using True A by (simp add: le_divide_eq)
  have hq: "A \<le> S * T ^ 2 / 4"
  proof (cases "S * T \<le> 2 * G")
    case True
    thus ?thesis using hI unfolding ramp_I_def by simp
  next
    case False
    have hG: "G \<le> S * T / 2" using False by linarith
    have "G ^ 2 \<le> (S * T / 2) ^ 2" by (rule power_mono[OF hG]) (use G in simp)
    moreover have "(S * T / 2) ^ 2 = S * (S * T ^ 2 / 4)" by (simp add: power2_eq_square field_simps)
    ultimately have "S * A \<le> S * (S * T ^ 2 / 4)" using hAS by linarith
    thus ?thesis by (simp only: mult_le_cancel_left_pos[OF S])
  qed
  have "2 * sqrt (A / S) \<le> T" by (rule tri_time[OF A S less_imp_le[OF T] hq])
  thus ?thesis unfolding ramp_Tmin_def using True by simp
next
  case False
  have hAS: "G ^ 2 < S * A"
  proof -
    have "G ^ 2 / A < S" using False by simp
    thus ?thesis by (simp only: pos_divide_less_eq[OF A])
  qed
  have tr: "2 * G < S * T"
  proof (rule ccontr)
    assume "\<not> 2 * G < S * T"
    hence le: "S * T \<le> 2 * G" by simp
    have hq: "A \<le> S * T ^ 2 / 4" using hI le unfolding ramp_I_def by simp
    have "(S * T) ^ 2 \<le> (2 * G) ^ 2" by (rule power_mono[OF le]) (use S T in simp)
    moreover have "(S * T) ^ 2 = S * (S * T ^ 2)" by (simp add: power2_eq_square field_simps)
    moreover have "S * A \<le> S * (S * T ^ 2 / 4)" by (rule mult_left_mono[OF hq]) (use S in simp)
    moreover have e2: "(2 * G) ^ 2 = 4 * G ^ 2" by (simp add: power_mult_distrib)
    moreover have e3: "S * (S * T ^ 2 / 4) = S * (S * T ^ 2) / 4" by simp
    ultimately show False using hAS by linarith
  qed
  have hI2: "A \<le> G * T - G ^ 2 / S" using hI tr unfolding ramp_I_def by simp
  have eq: "A / G + G / S = (A + G ^ 2 / S) / G" using G S by (simp add: field_simps power2_eq_square)
  have "A + G ^ 2 / S \<le> T * G" using hI2 by (simp add: algebra_simps)
  hence "(A + G ^ 2 / S) / G \<le> T" by (simp only: pos_divide_le_eq[OF G])
  thus ?thesis unfolding ramp_Tmin_def using False eq by simp
qed

theorem ramp_min_time_conv:
  fixes A S G T :: real
  assumes A: "0 < A" and S: "0 < S" and G: "0 < G" and T: "0 < T"
    and hT: "ramp_Tmin A S G \<le> T"
  shows "A \<le> ramp_I S G T"
proof (cases "S \<le> G ^ 2 / A")
  case True
  have hAS: "S * A \<le> G ^ 2" using True A by (simp add: le_divide_eq)
  have hq: "A \<le> S * T ^ 2 / 4"
    by (rule tri_conv[OF A S less_imp_le[OF T]]) (use hT True in \<open>simp add: ramp_Tmin_def\<close>)
  show ?thesis
  proof (cases "S * T \<le> 2 * G")
    case True
    thus ?thesis using hq unfolding ramp_I_def by simp
  next
    case False
    have "2 * G / S < T" using False S by (simp add: divide_less_eq mult.commute)
    hence "G * (2 * G / S) \<le> G * T" by (intro mult_left_mono) (use G in simp_all)
    moreover have "G * (2 * G / S) = 2 * (G ^ 2 / S)" by (simp add: power2_eq_square field_simps)
    moreover have "A \<le> G ^ 2 / S" using hAS S by (simp add: le_divide_eq mult.commute)
    ultimately have "A \<le> G * T - G ^ 2 / S" by linarith
    thus ?thesis unfolding ramp_I_def using False by simp
  qed
next
  case False
  have hAS: "G ^ 2 < S * A"
  proof -
    have "G ^ 2 / A < S" using False by simp
    thus ?thesis by (simp only: pos_divide_less_eq[OF A])
  qed
  have hT2: "A / G + G / S \<le> T" using hT False unfolding ramp_Tmin_def by simp
  have mul: "(A / G + G / S) * (S * G) = S * A + G ^ 2" using G S by (simp add: field_simps power2_eq_square)
  have "(A / G + G / S) * (S * G) \<le> T * (S * G)" by (rule mult_right_mono[OF hT2]) (use S G in simp)
  hence big: "S * A + G ^ 2 \<le> T * (S * G)" using mul by simp
  have tr: "2 * G < S * T"
  proof (rule ccontr)
    assume "\<not> 2 * G < S * T"
    hence "G * (S * T) \<le> G * (2 * G)" by (intro mult_left_mono) (use G in simp_all)
    thus False using big hAS by (simp add: power2_eq_square algebra_simps)
  qed
  have "(A / G + G / S) * G = A + G ^ 2 / S" using G S by (simp add: field_simps power2_eq_square)
  moreover have "(A / G + G / S) * G \<le> T * G" by (rule mult_right_mono[OF hT2]) (use G in simp)
  ultimately have "A + G ^ 2 / S \<le> G * T" by (simp add: mult.commute)
  thus ?thesis using tr unfolding ramp_I_def by simp
qed

section \<open>Minimal transfer time with ramped couplings\<close>

text \<open>If the derivatives of the moduli of the amplitudes of the two qubits are bounded by the trapezoidal
envelope times the square root of the bus occupation, the transfer takes at least the minimal time of the
ramped envelope with A = pi / sqrt 2. The ramp envelope lemma of the theory on weighted forms of the loss
floor (stated for the lemma named ramp envelope there) gives this envelope bound from couplings
that are Lipschitz with constant S, vanish at 0 and at T, and are bounded by G.\<close>

theorem ramped_transfer_time:
  fixes x z x' z' :: "real \<Rightarrow> real" and S G T :: real and E :: "real set"
  assumes S: "0 < S" and G: "0 < G" and T: "0 \<le> T" and E: "countable E"
    and cx: "continuous_on {0..T} x" and cz: "continuous_on {0..T} z"
    and D: "\<forall>t\<in>{0..T}. 0 \<le> x t \<and> 0 \<le> z t \<and> (x t)^2 + (z t)^2 \<le> 1"
    and x0: "x 0 = 1" and zT: "z T = 1"
    and der: "\<forall>t\<in>{0<..<T} - E. (x has_real_derivative x' t) (at t) \<and> (z has_real_derivative z' t) (at t)"
    and bnd: "\<forall>t\<in>{0<..<T} - E. \<bar>x' t\<bar> \<le> ramp_env S G T t * sqrt (1 - (x t)^2 - (z t)^2)
      \<and> \<bar>z' t\<bar> \<le> ramp_env S G T t * sqrt (1 - (x t)^2 - (z t)^2)"
  shows "ramp_Tmin (pi / sqrt 2) S G \<le> T"
proof -
  have A: "0 < pi / sqrt 2" by simp
  have key: "pi / sqrt 2 \<le> integral {0..T} (ramp_env S G T)"
    by (rule relay_minimal_time_var[OF T E cx cz D x0 zT der ramp_env_cont _ bnd])
       (use S G in \<open>simp add: ramp_env_nonneg\<close>)
  show ?thesis
  proof (cases "T = 0")
    case True
    thus ?thesis using key A by simp
  next
    case False
    hence Tp: "0 < T" using T by simp
    have "integral {0..T} (ramp_env S G T) = ramp_I S G T"
      by (rule integral_unique[OF ramp_env_integral[OF S G Tp]])
    thus ?thesis using key by (intro ramp_min_time[OF A S G Tp]) simp
  qed
qed

end
