(*  Title:      Relay_Loss_Floor.thy
    Author:     Carles Marín
    Copyright (c) 2026 Carles Marín. All rights reserved.
    License:    BSD

    Exact error floor of the relay with a lossy bus, and the time--occupation frontier for partial
    transfer with loss on the bus.
*)
theory Relay_Loss_Floor
  imports Relay_Occupation Relay_Dephasing
begin

text \<open>Two results on the relay qubit--bus--qubit with couplings bounded by |g| <= G when the qubits
lose population at rate gamma and the bus at rate kappa >= gamma. Multiplying the amplitudes by
exp(gamma t / 2) removes the loss of the qubits and leaves the bus with the excess rate
delta = kappa - gamma. Throughout, n denotes the squared norm of the rescaled state, y the modulus
of the rescaled bus amplitude (y squared is the occupation of the bus) and z the modulus of the
rescaled receiver amplitude. The Cauchy--Schwarz inequality and the fundamental theorem of calculus
with countably many exceptions are taken from the theories on the integrated occupation and on
dephasing of this entry.\<close>

section \<open>Auxiliary lemmas\<close>

text \<open>One-sided fundamental theorem of calculus: a derivative bounded above by -delta y\<^latex>\<open>\textsuperscript{2}\<close> off a
countable set bounds the decrease of the norm by -delta times the integrated occupation.\<close>

lemma ftc_decrease:
  fixes n n' y :: "real \<Rightarrow> real" and T \<delta> :: real and S :: "real set"
  assumes S: "countable S" and T: "0 < T"
    and nc: "continuous_on {0..T} n" and yc: "continuous_on {0..T} y"
    and der: "\<And>t. t \<in> {0<..<T} - S \<Longrightarrow> (n has_real_derivative n' t) (at t) \<and> n' t \<le> - \<delta> * (y t)\<^sup>2"
  shows "n T - n 0 \<le> - \<delta> * integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
proof -
  define f where "f = (\<lambda>t. if t \<in> {0<..<T} - S then n' t else - \<delta> * (y t)\<^sup>2)"
  have fd: "\<And>t. t \<in> {0<..<T} - S \<Longrightarrow> (n has_vector_derivative f t) (at t)"
  proof -
    fix t assume t: "t \<in> {0<..<T} - S"
    have "f t = n' t" unfolding f_def using t by simp
    thus "(n has_vector_derivative f t) (at t)" using der[OF t] by (simp add: has_real_derivative_iff_has_vector_derivative)
  qed
  have ftc: "(f has_integral n T - n 0) {0..T}"
    by (rule fundamental_theorem_of_calculus_interior_strong[OF S less_imp_le[OF T] fd nc])
  have y2c: "continuous_on {0..T} (\<lambda>t. (y t)\<^sup>2)" using yc by (intro continuous_intros)
  define J where "J = integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
  have y2i: "((\<lambda>t. (y t)\<^sup>2) has_integral J) {0..T}" unfolding J_def
    using integrable_continuous_real[OF y2c] by (rule integrable_integral)
  have gi: "((\<lambda>t. - \<delta> * (y t)\<^sup>2) has_integral - \<delta> * J) {0..T}"
    using has_integral_mult_right[OF y2i, of "- \<delta>"] by simp
  have fle: "\<And>t. t \<in> {0..T} \<Longrightarrow> f t \<le> - \<delta> * (y t)\<^sup>2"
  proof -
    fix t assume "t \<in> {0..T}"
    show "f t \<le> - \<delta> * (y t)\<^sup>2"
    proof (cases "t \<in> {0<..<T} - S")
      case True
      hence "f t = n' t" unfolding f_def by (rule if_P)
      thus ?thesis using der[OF True] by simp
    next
      case False
      hence "f t = - \<delta> * (y t)\<^sup>2" unfolding f_def by (rule if_not_P)
      thus ?thesis by simp
    qed
  qed
  show ?thesis unfolding J_def[symmetric] by (rule has_integral_le[OF ftc gi fle])
qed

section \<open>The exact error floor\<close>

text \<open>For any control with |z'| <= G y and n' <= -delta y\<^latex>\<open>\textsuperscript{2}\<close>, starting from a normalised state
(n 0 <= 1) and ending with z(T)\<^latex>\<open>\textsuperscript{2}\<close> <= n(T), the receiver satisfies
z(T)\<^latex>\<open>\textsuperscript{2}\<close> (1 + delta / (G\<^latex>\<open>\textsuperscript{2}\<close> T)) <= 1. In the original variables this reads
P(T) <= exp(-gamma T) / (1 + delta / (G\<^latex>\<open>\textsuperscript{2}\<close> T)) for every control and every duration T: the
transfer probability is the qubit-limited value divided by a factor that grows with the excess loss
delta of the bus and shrinks with G\<^latex>\<open>\textsuperscript{2}\<close> T.\<close>

theorem loss_floor:
  fixes n y z n' z' :: "real \<Rightarrow> real" and G T \<delta> :: real and S :: "real set"
  assumes T: "0 < T" and G: "0 < G" and d0: "0 \<le> \<delta>" and S: "countable S"
    and nc: "continuous_on {0..T} n" and yc: "continuous_on {0..T} y" and zc: "continuous_on {0..T} z"
    and y0: "\<forall>t\<in>{0..T}. 0 \<le> y t"
    and n0: "n 0 \<le> 1" and z0: "z 0 = 0" and zT: "(z T)\<^sup>2 \<le> n T"
    and der: "\<forall>t\<in>{0<..<T} - S. (n has_real_derivative n' t) (at t) \<and> (z has_real_derivative z' t) (at t)"
    and bnd: "\<forall>t\<in>{0<..<T} - S. n' t \<le> - \<delta> * (y t)\<^sup>2 \<and> \<bar>z' t\<bar> \<le> G * y t"
  shows "(z T)\<^sup>2 * (1 + \<delta> / (G\<^sup>2 * T)) \<le> 1"
proof -
  define I where "I = integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
  define A where "A = (z T)\<^sup>2"
  have s1: "n T - n 0 \<le> - \<delta> * I" unfolding I_def
    by (rule ftc_decrease[OF S T nc yc]) (use der bnd in blast)
  have s1': "\<delta> * I \<le> 1 - A" using s1 n0 zT unfolding A_def by linarith
  have Gyc: "continuous_on {0..T} (\<lambda>t. G * y t)" using yc by (intro continuous_intros)
  have b2: "\<bar>z T - z 0\<bar> \<le> integral {0..T} (\<lambda>t. G * y t)"
    by (rule ftc_bound[where F' = z', OF S less_imp_le[OF T] zc Gyc]) (use G y0 der bnd in auto)
  have yi: "(y has_integral integral {0..T} y) {0..T}"
    using integrable_continuous_real[OF yc] by (rule integrable_integral)
  have "integral {0..T} (\<lambda>t. G * y t) = G * integral {0..T} y"
    using integral_unique[OF has_integral_mult_right[OF yi, of G]] by simp
  hence "\<bar>z T\<bar> \<le> G * integral {0..T} y" using b2 z0 by simp
  hence "(z T)\<^sup>2 \<le> (G * integral {0..T} y)\<^sup>2"
    using power_mono[of "\<bar>z T\<bar>" _ 2] abs_ge_zero by simp
  also have "\<dots> = G\<^sup>2 * (integral {0..T} y)\<^sup>2" by (simp add: power_mult_distrib)
  also have "\<dots> \<le> G\<^sup>2 * (T * I)" unfolding I_def
    by (rule mult_left_mono[OF cauchy_schwarz_cont[OF T yc]]) simp
  finally have s2: "A \<le> G\<^sup>2 * T * I" unfolding A_def by (simp add: mult.assoc)
  have "A / (G\<^sup>2 * T) \<le> I" using s2 G T by (simp add: pos_divide_le_eq mult.commute)
  hence "\<delta> * (A / (G\<^sup>2 * T)) \<le> \<delta> * I" using d0 by (rule mult_left_mono)
  hence "A * (\<delta> / (G\<^sup>2 * T)) \<le> \<delta> * I" by (simp add: algebra_simps)
  thus ?thesis unfolding A_def[symmetric] using s1' by (simp add: algebra_simps A_def)
qed

text \<open>One-sided fundamental theorem of calculus with a constant majorant.\<close>

lemma ftc_up:
  fixes F F' :: "real \<Rightarrow> real" and a b c :: real and S :: "real set"
  assumes S: "countable S" and ab: "a \<le> b" and c0: "0 \<le> c"
    and Fc: "continuous_on {a..b} F"
    and der: "\<And>t. t \<in> {a<..<b} - S \<Longrightarrow> (F has_real_derivative F' t) (at t) \<and> F' t \<le> c"
  shows "F b - F a \<le> c * (b - a)"
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
  have ci: "((\<lambda>t. c) has_integral c * (b - a)) {a..b}"
    using has_integral_const_real[of c a b] ab by (simp add: mult.commute)
  have fle: "\<And>t. t \<in> {a..b} \<Longrightarrow> f t \<le> c"
  proof -
    fix t assume t: "t \<in> {a..b}"
    show "f t \<le> c"
    proof (cases "t \<in> {a<..<b} - S")
      case True
      hence "f t = F' t" unfolding f_def by (rule if_P)
      thus ?thesis using der[OF True] by simp
    next
      case False
      hence "f t = 0" unfolding f_def by (rule if_not_P)
      thus ?thesis using c0 by simp
    qed
  qed
  show ?thesis by (rule has_integral_le[OF ftc ci fle])
qed

text \<open>Upper growth bound of the square root of a nonnegative function with p' <= 2 sqrt 2 G sqrt p.\<close>

lemma sqrt_growth:
  fixes p p' :: "real \<Rightarrow> real" and G a b :: real and S :: "real set"
  assumes S: "countable S" and G: "0 < G" and ab: "a \<le> b"
    and pc: "continuous_on {a..b} p" and pnn: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> p t"
    and der: "\<And>t. t \<in> {a<..<b} - S \<Longrightarrow> (p has_real_derivative p' t) (at t) \<and> p' t \<le> 2 * sqrt 2 * G * sqrt (p t)"
  shows "sqrt (p b) - sqrt (p a) \<le> sqrt 2 * G * (b - a)"
proof (rule field_le_epsilon)
  fix e :: real assume e: "0 < e"
  define F where "F = (\<lambda>t. sqrt (p t + e\<^sup>2))"
  define F' where "F' = (\<lambda>t. inverse (sqrt (p t + e\<^sup>2)) / 2 * p' t)"
  have pe: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 < p t + e\<^sup>2" using pnn e by (simp add: add_nonneg_pos)
  have Fc: "continuous_on {a..b} F" unfolding F_def
    by (rule continuous_on_compose2[OF continuous_on_real_sqrt]) (use pc pe in \<open>auto intro!: continuous_intros\<close>)
  have c0: "0 \<le> sqrt 2 * G" using G by simp
  have "F b - F a \<le> sqrt 2 * G * (b - a)"
  proof (rule ftc_up[OF S ab c0 Fc, where F' = F'])
    fix t assume t: "t \<in> {a<..<b} - S"
    hence tt: "t \<in> {a..b}" by auto
    from der[OF t] have hp: "(p has_real_derivative p' t) (at t)" and pb: "p' t \<le> 2 * sqrt 2 * G * sqrt (p t)" by blast+
    have pt: "0 < p t + e\<^sup>2" by (rule pe[OF tt])
    have d1: "(sqrt has_real_derivative inverse (sqrt (p t + e\<^sup>2)) / 2) (at (p t + e\<^sup>2))"
      by (rule DERIV_real_sqrt[OF pt])
    have d2: "((\<lambda>t. p t + e\<^sup>2) has_real_derivative p' t) (at t)" using hp by (auto intro!: derivative_eq_intros)
    have dF: "(F has_real_derivative F' t) (at t)" unfolding F_def F'_def
      using DERIV_chain2[OF d1 d2] by simp
    define r where "r = sqrt (p t + e\<^sup>2)"
    have r0: "0 < r" unfolding r_def using pt by simp
    have sp: "sqrt (p t) \<le> r" unfolding r_def by (rule real_sqrt_le_mono) (use e in simp)
    have "F' t \<le> inverse r / 2 * (2 * sqrt 2 * G * sqrt (p t))"
      unfolding F'_def r_def[symmetric] by (rule mult_left_mono[OF pb]) (use r0 in simp)
    also have "... = sqrt 2 * G * (sqrt (p t) / r)" by (simp add: field_simps)
    also have "... \<le> sqrt 2 * G * 1"
      by (rule mult_left_mono) (use sp r0 c0 in \<open>auto simp: divide_le_eq_1\<close>)
    finally show "(F has_real_derivative F' t) (at t) \<and> F' t \<le> sqrt 2 * G" using dF by simp
  qed
  moreover have "sqrt (p b) \<le> F b" unfolding F_def by (rule real_sqrt_le_mono) simp
  moreover have "F a \<le> sqrt (p a) + e"
  proof -
    have "sqrt (p a + e\<^sup>2) \<le> sqrt (p a) + sqrt (e\<^sup>2)"
      by (rule sqrt_add_le_add_sqrt) (use pnn[of a] ab in auto)
    thus ?thesis unfolding F_def using e by simp
  qed
  ultimately show "sqrt (p b) - sqrt (p a) \<le> sqrt 2 * G * (b - a) + e" by linarith
qed

text \<open>Area under the rising half-parabola.\<close>

lemma cubic_int:
  fixes M yc tc w :: real
  assumes "0 < M" "0 \<le> w" "yc = M * w"
  shows "((\<lambda>t. (yc - M * (tc - t))\<^sup>2) has_integral yc ^ 3 / (3 * M)) {tc - w..tc}"
proof -
  let ?F = "\<lambda>t::real. (yc - M * (tc - t)) ^ 3 / (3 * M)"
  have h1: "((\<lambda>t. (yc - M * (tc - t))\<^sup>2) has_integral ?F tc - ?F (tc - w)) {tc - w..tc}"
  proof (rule ftc_real)
    show "tc - w \<le> tc" using assms(2) by simp
    fix t :: real
    have "(?F has_real_derivative (3 * (yc - M * (tc - t)) ^ 2 * M) / (3 * M)) (at t)"
      by (auto intro!: derivative_eq_intros)
    moreover have "(3 * (yc - M * (tc - t)) ^ 2 * M) / (3 * M) = (yc - M * (tc - t))\<^sup>2"
      using assms(1) by (simp add: field_simps)
    ultimately show "(?F has_real_derivative (yc - M * (tc - t))\<^sup>2) (at t)" by simp
  qed
  have h2: "?F tc - ?F (tc - w) = yc ^ 3 / (3 * M)"
  proof -
    have "yc - M * (tc - (tc - w)) = 0" using assms(3) by simp
    thus ?thesis by simp
  qed
  show ?thesis by (rule h1[unfolded h2])
qed

section \<open>The frontier with partial transfer\<close>

text \<open>Time--occupation frontier for a partial transfer with loss on the bus. Here x and z are the
moduli of the amplitudes of the two qubits and p the occupation of the bus, with
x\<^latex>\<open>\textsuperscript{2}\<close> + z\<^latex>\<open>\textsuperscript{2}\<close> + p <= 1; the remainder is lost. Transfer is partial: z(T)\<^latex>\<open>\textsuperscript{2}\<close> >= 1 - epsilon
with epsilon <= 1/2, and the total population stays above 1 - epsilon. The coupling bounds are
|x'|, |z'| <= G sqrt p and p' <= 2 sqrt 2 G sqrt p. The theorem gives a level yc in [0,1] of the
modulus of the bus amplitude at a crossing time of x and z at which two lower bounds on the
integrated occupation hold together: the transport bound
(max 0 (sqrt (2 (1 - epsilon - yc\<^latex>\<open>\textsuperscript{2}\<close>)) - sqrt epsilon))\<^latex>\<open>\textsuperscript{2}\<close> <= G\<^latex>\<open>\textsuperscript{2}\<close> T (integral of p), and the
backward-window bound (sqrt 2 / 6) yc\<^latex>\<open>\textsuperscript{3}\<close> <= G (integral of p). As G T tends to infinity and epsilon
to 0, they force G\<^latex>\<open>\textsuperscript{2}\<close> T (integral of p) to be at least 2 - o(1).\<close>

theorem partial_frontier:
  fixes x z p x' z' p' :: "real \<Rightarrow> real" and G T \<epsilon> :: real and S :: "real set"
  assumes T: "0 < T" and G: "0 < G" and S: "countable S"
    and cx: "continuous_on {0..T} x" and cz: "continuous_on {0..T} z" and cp: "continuous_on {0..T} p"
    and D: "\<forall>t\<in>{0..T}. 0 \<le> x t \<and> 0 \<le> z t \<and> 0 \<le> p t \<and> (x t)\<^sup>2 + (z t)\<^sup>2 + p t \<le> 1"
    and x0: "x 0 = 1" and z0: "z 0 = 0" and p0: "p 0 = 0"
    and e0: "0 \<le> \<epsilon>" and e1: "\<epsilon> \<le> 1 / 2" and zT: "1 - \<epsilon> \<le> (z T)\<^sup>2"
    and nT: "\<forall>t\<in>{0..T}. 1 - \<epsilon> \<le> (x t)\<^sup>2 + (z t)\<^sup>2 + p t"
    and der: "\<forall>t\<in>{0<..<T} - S. (x has_real_derivative x' t) (at t) \<and> (z has_real_derivative z' t) (at t) \<and> (p has_real_derivative p' t) (at t)"
    and bnd: "\<forall>t\<in>{0<..<T} - S. \<bar>x' t\<bar> \<le> G * sqrt (p t) \<and> \<bar>z' t\<bar> \<le> G * sqrt (p t) \<and> p' t \<le> 2 * sqrt 2 * G * sqrt (p t)"
  shows "\<exists>yc\<in>{0..1}. (max 0 (sqrt (2 * (1 - \<epsilon> - yc\<^sup>2)) - sqrt \<epsilon>))\<^sup>2 \<le> G\<^sup>2 * T * integral {0..T} p
                    \<and> sqrt 2 / 6 * yc ^ 3 \<le> G * integral {0..T} p"
proof -
  define y where "y = (\<lambda>t. sqrt (p t))"
  have Dt: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> x t \<and> 0 \<le> z t \<and> 0 \<le> p t \<and> (x t)\<^sup>2 + (z t)\<^sup>2 + p t \<le> 1" using D by blast
  have pnn: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> p t" using Dt by blast
  have y0: "\<And>t. t \<in> {0..T} \<Longrightarrow> 0 \<le> y t" unfolding y_def using pnn by simp
  have y2: "\<And>t. t \<in> {0..T} \<Longrightarrow> (y t)\<^sup>2 = p t" unfolding y_def using pnn by simp
  have yc: "continuous_on {0..T} y" unfolding y_def
    by (rule continuous_on_compose2[OF continuous_on_real_sqrt cp]) (use pnn in auto)
  have bnd': "\<And>t. t \<in> {0<..<T} - S \<Longrightarrow> \<bar>x' t\<bar> \<le> G * y t \<and> \<bar>z' t\<bar> \<le> G * y t"
    using bnd unfolding y_def by blast
  have zT0: "0 \<le> z T" using Dt[of T] T by auto
  have xT0: "0 \<le> x T" using Dt[of T] T by auto
  have xT2: "(x T)\<^sup>2 \<le> \<epsilon>"
  proof -
    have "(x T)\<^sup>2 + (z T)\<^sup>2 + p T \<le> 1" "0 \<le> p T" using Dt[of T] T by auto
    thus ?thesis using zT by linarith
  qed
  have xTe: "x T \<le> sqrt \<epsilon>" by (rule real_le_rsqrt[OF xT2])
  have xTz: "x T \<le> z T"
  proof (rule power2_le_imp_le[OF _ zT0])
    show "(x T)\<^sup>2 \<le> (z T)\<^sup>2" using xT2 zT e1 by linarith
  qed
  \<comment> \<open>crossing\<close>
  obtain tc where tcr: "0 \<le> tc" "tc \<le> T" and tcxz: "x tc = z tc"
  proof -
    have cg: "continuous_on {0..T} (\<lambda>t. x t - z t)" using cx cz by (intro continuous_intros)
    have conn: "connected ((\<lambda>t. x t - z t) ` {0..T})"
      by (rule connected_continuous_image[OF cg connected_Icc])
    have m1: "(x T - z T) \<in> (\<lambda>t. x t - z t) ` {0..T}" using T by (intro image_eqI[of _ _ T]) auto
    have p1': "(1::real) \<in> (\<lambda>t. x t - z t) ` {0..T}" using x0 z0 T by (intro image_eqI[of _ _ 0]) auto
    have "{x T - z T..1} \<subseteq> (\<lambda>t. x t - z t) ` {0..T}" by (rule connected_contains_Icc[OF conn m1 p1'])
    moreover have "(0::real) \<in> {x T - z T..1}" using xTz by simp
    ultimately have "(0::real) \<in> (\<lambda>t. x t - z t) ` {0..T}" by blast
    then obtain t where "t \<in> {0..T}" "x t - z t = 0" by auto
    thus ?thesis using that by auto
  qed
  have tcD: "tc \<in> {0..T}" using tcr by simp
  define s where "s = z tc"
  have xs: "x tc = s" unfolding s_def by (rule tcxz)
  have s0: "0 \<le> s" unfolding s_def using Dt[OF tcD] by simp
  define yc where "yc = y tc"
  have yc0: "0 \<le> yc" unfolding yc_def using y0[OF tcD] .
  have yc2: "yc\<^sup>2 = p tc" unfolding yc_def using y2[OF tcD] .
  have yc1: "yc \<le> 1"
  proof -
    have "p tc \<le> 1" using Dt[OF tcD] zero_le_power2[of "x tc"] zero_le_power2[of "z tc"] by linarith
    have "yc\<^sup>2 \<le> 1\<^sup>2" using yc2 \<open>p tc \<le> 1\<close> by simp
    thus ?thesis by (rule power2_le_imp_le) simp
  qed
  have hyp: "1 - \<epsilon> \<le> 2 * s\<^sup>2 + yc\<^sup>2"
    using nT[rule_format, OF tcD] xs yc2 unfolding s_def by simp
  \<comment> \<open>first inequality\<close>
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
  have Iy0: "0 \<le> Iy" by (rule has_integral_nonneg[OF yi]) (use y0 in auto)
  have Gyh: "((\<lambda>t. G * y t) has_integral G * Iy) {0..T}" using has_integral_mult_right[OF yi, of G] by simp
  have comb: "integral {0..tc} (\<lambda>t. G * y t) + integral {tc..T} (\<lambda>t. G * y t) = G * Iy"
  proof -
    have "integral {0..tc} (\<lambda>t. G * y t) + integral {tc..T} (\<lambda>t. G * y t) = integral {0..T} (\<lambda>t. G * y t)"
      by (rule Henstock_Kurzweil_Integration.integral_combine[OF tcr(1) tcr(2) Gyi[OF order_refl order_refl]])
    thus ?thesis by (rule trans[OF _ integral_unique[OF Gyh]])
  qed
  have s_le1: "s \<le> integral {0..tc} (\<lambda>t. G * y t)" using bz z0 unfolding s_def by (simp add: abs_le_iff)
  have s_le2: "s - x T \<le> integral {tc..T} (\<lambda>t. G * y t)" using bx xs by (simp add: abs_le_iff)
  have s2G: "2 * s - x T \<le> G * Iy" using s_le1 s_le2 comb by linarith
  have sq: "sqrt (2 * (1 - \<epsilon> - yc\<^sup>2)) \<le> 2 * s"
  proof -
    have "2 * (1 - \<epsilon> - yc\<^sup>2) \<le> (2 * s)\<^sup>2" using hyp by (simp add: power_mult_distrib)
    hence "sqrt (2 * (1 - \<epsilon> - yc\<^sup>2)) \<le> sqrt ((2 * s)\<^sup>2)" by (rule real_sqrt_le_mono)
    moreover have "sqrt ((2 * s)\<^sup>2) = 2 * s" 
    proof -
      have "sqrt ((2 * s)\<^sup>2) = \<bar>2 * s\<bar>" by (rule real_sqrt_abs)
      also have "... = 2 * s" using s0 by simp
      finally show ?thesis .
    qed
    ultimately show ?thesis by (rule ord_le_eq_trans)
  qed
  have mle: "max 0 (sqrt (2 * (1 - \<epsilon> - yc\<^sup>2)) - sqrt \<epsilon>) \<le> G * Iy"
    using sq s2G xTe Iy0 G by (intro max.boundedI) (auto intro!: mult_nonneg_nonneg)
  have cs: "Iy\<^sup>2 \<le> T * integral {0..T} (\<lambda>t. (y t)\<^sup>2)"
    unfolding Iy_def by (rule cauchy_schwarz_cont[OF T yc])
  define I where "I = integral {0..T} p"
  have Iyp: "integral {0..T} (\<lambda>t. (y t)\<^sup>2) = I" unfolding I_def by (rule integral_cong) (simp add: y2)
  have first: "(max 0 (sqrt (2 * (1 - \<epsilon> - yc\<^sup>2)) - sqrt \<epsilon>))\<^sup>2 \<le> G\<^sup>2 * T * I"
  proof -
    have "(max 0 (sqrt (2 * (1 - \<epsilon> - yc\<^sup>2)) - sqrt \<epsilon>))\<^sup>2 \<le> (G * Iy)\<^sup>2"
      by (rule power_mono[OF mle]) simp
    also have "... = G\<^sup>2 * Iy\<^sup>2" by (simp add: power_mult_distrib)
    also have "... \<le> G\<^sup>2 * (T * I)" using cs Iyp by (intro mult_left_mono) auto
    finally show ?thesis by (simp add: algebra_simps)
  qed
  \<comment> \<open>backward window\<close>
  define M where "M = sqrt 2 * G"
  have M0: "0 < M" unfolding M_def using G by simp
  have grow: "\<And>t. t \<in> {0..tc} \<Longrightarrow> yc - M * (tc - t) \<le> y t"
  proof -
    fix t assume t: "t \<in> {0..tc}"
    have "sqrt (p tc) - sqrt (p t) \<le> sqrt 2 * G * (tc - t)"
    proof (rule sqrt_growth[OF S G _ _ _])
      show "t \<le> tc" using t by simp
      show "continuous_on {t..tc} p" by (rule continuous_on_subset[OF cp]) (use t tcr in auto)
      show "\<And>u. u \<in> {t..tc} \<Longrightarrow> 0 \<le> p u" using pnn t tcr by auto
      fix u assume u: "u \<in> {t<..<tc} - S"
      hence uu: "u \<in> {0<..<T} - S" using t tcr by auto
      show "(p has_real_derivative p' u) (at u) \<and> p' u \<le> 2 * sqrt 2 * G * sqrt (p u)" using der bnd uu by blast
    qed
    thus "yc - M * (tc - t) \<le> y t" unfolding yc_def y_def M_def by simp
  qed
  have yc_le: "yc \<le> M * tc" using grow[of 0] tcr y_def p0 by (simp add: y_def p0)
  define w where "w = yc / M"
  have w0: "0 \<le> w" unfolding w_def using yc0 M0 by simp
  have ycw: "yc = M * w" unfolding w_def using M0 by simp
  have wtc: "w \<le> tc" unfolding w_def using yc_le M0 by (simp add: divide_le_eq mult.commute)
  define a1 where "a1 = tc - w"
  have a1r: "0 \<le> a1" "a1 \<le> tc" unfolding a1_def using wtc w0 by auto
  have pint: "\<And>a::real. \<And>b::real. 0 \<le> a \<Longrightarrow> b \<le> T \<Longrightarrow> (p has_integral integral {a..b} p) {a..b}"
  proof -
    fix a b :: real assume "0 \<le> a" "b \<le> T"
    have "p integrable_on {a..b}"
      by (rule integrable_continuous_real, rule continuous_on_subset[OF cp]) (use \<open>0 \<le> a\<close> \<open>b \<le> T\<close> in auto)
    thus "(p has_integral integral {a..b} p) {a..b}" by (rule integrable_integral)
  qed
  have pi_sub: "\<And>a::real. \<And>b::real. 0 \<le> a \<Longrightarrow> b \<le> T \<Longrightarrow> p integrable_on {a..b}"
    using pint by (auto simp: has_integral_integrable)
  have nn_int: "\<And>a::real. \<And>b::real. 0 \<le> a \<Longrightarrow> a \<le> b \<Longrightarrow> b \<le> T \<Longrightarrow> 0 \<le> integral {a..b} p"
    by (rule has_integral_nonneg[OF pint]) (use pnn in auto)
  have L: "yc ^ 3 / (3 * M) \<le> integral {a1..tc} p"
  proof -
    have cb: "((\<lambda>t. (yc - M * (tc - t))\<^sup>2) has_integral yc ^ 3 / (3 * M)) {a1..tc}"
      unfolding a1_def by (rule cubic_int[OF M0 w0 ycw])
    have ineq: "\<And>t. t \<in> {a1..tc} \<Longrightarrow> (yc - M * (tc - t))\<^sup>2 \<le> p t"
    proof -
      fix t assume t: "t \<in> {a1..tc}"
      hence tD: "t \<in> {0..T}" and t0: "t \<in> {0..tc}" using a1r tcr by auto
      have "M * (tc - t) \<le> M * w" using t unfolding a1_def by (intro mult_left_mono) (use M0 in auto)
      hence lo: "0 \<le> yc - M * (tc - t)" using ycw by simp
      have "(yc - M * (tc - t))\<^sup>2 \<le> (y t)\<^sup>2" by (rule power_mono[OF grow[OF t0] lo])
      thus "(yc - M * (tc - t))\<^sup>2 \<le> p t" using y2[OF tD] by simp
    qed
    show ?thesis by (rule has_integral_le[OF cb pint[OF a1r(1) tcr(2)] ineq])
  qed
  have c1: "integral {0..a1} p + integral {a1..tc} p = integral {0..tc} p"
    by (rule Henstock_Kurzweil_Integration.integral_combine[OF a1r(1) a1r(2) pi_sub[OF order_refl tcr(2)]])
  have c2: "integral {0..tc} p + integral {tc..T} p = I" unfolding I_def
    by (rule Henstock_Kurzweil_Integration.integral_combine[OF tcr(1) tcr(2) pi_sub[OF order_refl order_refl]])
  have n1: "0 \<le> integral {0..a1} p" by (rule nn_int[OF order_refl a1r(1)]) (use a1r tcr in linarith)
  have n2: "0 \<le> integral {tc..T} p" by (rule nn_int[OF tcr(1) tcr(2) order_refl])
  have Ilow: "yc ^ 3 / (3 * M) \<le> I" using L c1 c2 n1 n2 by linarith
  have second: "sqrt 2 / 6 * yc ^ 3 \<le> G * I"
  proof -
    have r2: "sqrt 2 * sqrt 2 = (2::real)" by simp
    have "sqrt 2 / 6 * yc ^ 3 = G * (yc ^ 3 / (3 * M))"
      unfolding M_def using G by (simp add: field_simps r2)
    also have "... \<le> G * I" using Ilow G by (intro mult_left_mono) auto
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule bexI[of _ yc])
    show "(max 0 (sqrt (2 * (1 - \<epsilon> - yc\<^sup>2)) - sqrt \<epsilon>))\<^sup>2 \<le> G\<^sup>2 * T * integral {0..T} p
          \<and> sqrt 2 / 6 * yc ^ 3 \<le> G * integral {0..T} p"
      using first second unfolding I_def by blast
    show "yc \<in> {0..1}" using yc0 yc1 by simp
  qed
qed

end
