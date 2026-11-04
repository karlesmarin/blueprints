(* encaje: teoria Isabelle de la cola (formalizacion), compilada con isa_compilar.py; no es herramienta. *)
theory Relay_Coherence
  imports "HOL-Analysis.Analysis"
begin

text \<open>
Coherence is an amplitude. Index set is zero up to n. State zero is the vacuum and states one up to n
are the single excitation states. A density matrix is any function of two natural numbers with complex values.
The Hamiltonian conserves the excitation number: its row zero and column zero vanish.
The Lindblad operators are of two kinds for each j from one to n: relaxation with entry L zero j equal to the
square root of r j, and dephasing with entry L j j equal to the square root of d j.
All matrix products are finite sums over the index set.
\<close>

section \<open>Matrices as finite sums\<close>

definition mm :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "mm n A B a b = (\<Sum>k\<in>{0..n}. A a k * B k b)"

definition dag :: "(nat \<Rightarrow> nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "dag L a b = cnj (L b a)"

definition Lrel :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "Lrel r j a b = (if a = 0 \<and> b = j then of_real (sqrt (r j)) else 0)"

definition Ldeph :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "Ldeph d j a b = (if a = j \<and> b = j then of_real (sqrt (d j)) else 0)"

definition dissip :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "dissip n L rho a b =
     mm n (mm n L rho) (dag L) a b
     - (1/2) * (mm n (mm n (dag L) L) rho a b + mm n rho (mm n (dag L) L) a b)"

definition gen :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real)
    \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "gen n H r d rho a b =
     - \<i> * (mm n H rho a b - mm n rho H a b)
     + (\<Sum>j\<in>{1..n}. dissip n (Lrel r j) rho a b)
     + (\<Sum>j\<in>{1..n}. dissip n (Ldeph d j) rho a b)"

section \<open>The two Lindblad products\<close>

lemma dag_Lrel_Lrel:
  assumes "r j \<ge> 0" "j \<le> n"
  shows "mm n (dag (Lrel r j)) (Lrel r j) a b = (if a = j \<and> b = j then of_real (r j) else 0)"
proof -
  have h: "\<And>c. c \<in> {0..n} \<Longrightarrow> dag (Lrel r j) a c * Lrel r j c b
      = (if c = 0 then (if a = j \<and> b = j then of_real (r j) else 0) else 0)"
  proof -
    fix c assume "c \<in> {0..n}"
    have q: "sqrt (r j) * sqrt (r j) = r j" by (simp add: real_sqrt_mult_self abs_of_nonneg assms(1))
    have s: "of_real (sqrt (r j)) * of_real (sqrt (r j)) = (of_real (r j) :: complex)"
      by (simp only: of_real_mult[symmetric] q)
    show "dag (Lrel r j) a c * Lrel r j c b
      = (if c = 0 then (if a = j \<and> b = j then of_real (r j) else 0) else 0)"
      by (auto simp add: dag_def Lrel_def s)
  qed
  have "mm n (dag (Lrel r j)) (Lrel r j) a b
      = (\<Sum>c\<in>{0..n}. if c = 0 then (if a = j \<and> b = j then of_real (r j) else 0) else 0)"
    unfolding mm_def by (rule sum.cong[OF refl h])
  also have "\<dots> = (if a = j \<and> b = j then of_real (r j) else 0)"
    by (simp only: sum.delta[OF finite_atLeastAtMost] atLeastAtMost_iff, simp)
  finally show ?thesis .
qed

lemma dag_Ldeph_Ldeph:
  assumes "d j \<ge> 0" "j \<le> n"
  shows "mm n (dag (Ldeph d j)) (Ldeph d j) a b = (if a = j \<and> b = j then of_real (d j) else 0)"
proof -
  have h: "\<And>c. c \<in> {0..n} \<Longrightarrow> dag (Ldeph d j) a c * Ldeph d j c b
      = (if c = j then (if a = j \<and> b = j then of_real (d j) else 0) else 0)"
  proof -
    fix c assume "c \<in> {0..n}"
    have q: "sqrt (d j) * sqrt (d j) = d j" by (simp add: real_sqrt_mult_self abs_of_nonneg assms(1))
    have s: "of_real (sqrt (d j)) * of_real (sqrt (d j)) = (of_real (d j) :: complex)"
      by (simp only: of_real_mult[symmetric] q)
    show "dag (Ldeph d j) a c * Ldeph d j c b
      = (if c = j then (if a = j \<and> b = j then of_real (d j) else 0) else 0)"
      by (auto simp add: dag_def Ldeph_def s)
  qed
  have "mm n (dag (Ldeph d j)) (Ldeph d j) a b
      = (\<Sum>c\<in>{0..n}. if c = j then (if a = j \<and> b = j then of_real (d j) else 0) else 0)"
    unfolding mm_def by (rule sum.cong[OF refl h])
  also have "\<dots> = (if a = j \<and> b = j then of_real (d j) else 0)"
    using assms(2) by (simp only: sum.delta[OF finite_atLeastAtMost] atLeastAtMost_iff, simp)
  finally show ?thesis .
qed

section \<open>The dissipator on the entry j zero\<close>

text \<open>
For a Lindblad operator whose product with its adjoint is diagonal with weight w at m, and whose jump
term vanishes at the entry j zero, the dissipator at that entry is minus one half w times rho j zero
when j equals m, and zero otherwise.
\<close>

lemma dissip_vac:
  fixes L :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  assumes K: "\<And>a b. mm n (dag L) L a b = (if a = m \<and> b = m then w else 0)"
    and jump: "mm n (mm n L rho) (dag L) j 0 = 0"
    and m0: "m \<noteq> 0" and jn: "j \<le> n"
  shows "dissip n L rho j 0 = - (1/2) * (if j = m then w * rho j 0 else 0)"
proof -
  have e1: "mm n (mm n (dag L) L) rho j 0 = (if j = m then w * rho j 0 else 0)"
  proof -
    have h: "\<And>k. k \<in> {0..n} \<Longrightarrow> mm n (dag L) L j k * rho k 0
        = (if k = m then (if j = m then w * rho k 0 else 0) else 0)"
      by (auto simp add: K)
    have "mm n (mm n (dag L) L) rho j 0
        = (\<Sum>k\<in>{0..n}. if k = m then (if j = m then w * rho k 0 else 0) else 0)"
      by (subst mm_def[where A = "mm n (dag L) L" and B = rho and a = j and b = 0],
          rule sum.cong[OF refl h])
    also have "\<dots> = (if m \<in> {0..n} then (if j = m then w * rho m 0 else 0) else 0)"
      by (rule sum.delta[OF finite_atLeastAtMost])
    also have "\<dots> = (if j = m then w * rho j 0 else 0)"
      using jn by (auto simp add: atLeastAtMost_iff)
    finally show ?thesis .
  qed
  have e2: "mm n rho (mm n (dag L) L) j 0 = 0"
  proof -
    have h: "\<And>k. k \<in> {0..n} \<Longrightarrow> rho j k * mm n (dag L) L k 0 = 0"
      using m0 by (simp add: K)
    show ?thesis
      by (subst mm_def[where A = rho and B = "mm n (dag L) L" and a = j and b = 0],
          rule sum.neutral, simp add: h)
  qed
  show ?thesis
    unfolding dissip_def by (simp only: e1 e2 jump) simp
qed

section \<open>1. Vacuum coherence generator\<close>

definition Gam :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "Gam r d j = r j + d j"

lemma jump_rel:
  assumes "j \<ge> 1"
  shows "mm n (mm n (Lrel r m) rho) (dag (Lrel r m)) j 0 = 0"
  using assms by (simp add: mm_def Lrel_def)

lemma jump_deph:
  assumes "m \<noteq> 0"
  shows "mm n (mm n (Ldeph d m) rho) (dag (Ldeph d m)) j 0 = 0"
  using assms by (simp add: mm_def Ldeph_def dag_def)

theorem vacuum_coherence_generator:
  assumes H0: "\<And>k. H k 0 = 0"
    and r0: "\<And>j. r j \<ge> 0" and d0: "\<And>j. d j \<ge> 0"
    and j1: "1 \<le> j" and jn: "j \<le> n"
  shows "gen n H r d rho j 0
    = - \<i> * (\<Sum>k\<in>{1..n}. H j k * rho k 0) - (1/2) * of_real (Gam r d j) * rho j 0"
proof -
  have split: "{0..n} = insert 0 {1..n}" using jn by auto
  have ham1: "mm n rho H j 0 = 0"
    unfolding mm_def by (rule sum.neutral, simp add: H0)
  have ham2: "mm n H rho j 0 = (\<Sum>k\<in>{1..n}. H j k * rho k 0)"
  proof -
    have "mm n H rho j 0 = H j 0 * rho 0 0 + (\<Sum>k\<in>{1..n}. H j k * rho k 0)"
      unfolding mm_def split by simp
    thus ?thesis by (simp add: H0)
  qed
  have rel: "\<And>m. m \<in> {1..n} \<Longrightarrow> dissip n (Lrel r m) rho j 0
      = - (1/2) * (if j = m then of_real (r m) * rho j 0 else 0)"
  proof -
    fix m assume m: "m \<in> {1..n}"
    have K: "\<And>a b. mm n (dag (Lrel r m)) (Lrel r m) a b
        = (if a = m \<and> b = m then of_real (r m) else 0)"
      using m by (intro dag_Lrel_Lrel r0, simp)
    show "dissip n (Lrel r m) rho j 0 = - (1/2) * (if j = m then of_real (r m) * rho j 0 else 0)"
      using m by (intro dissip_vac[where w = "of_real (r m)" and m = m, OF K jump_rel[OF j1] _ jn], simp)
  qed
  have dep: "\<And>m. m \<in> {1..n} \<Longrightarrow> dissip n (Ldeph d m) rho j 0
      = - (1/2) * (if j = m then of_real (d m) * rho j 0 else 0)"
  proof -
    fix m assume m: "m \<in> {1..n}"
    have K: "\<And>a b. mm n (dag (Ldeph d m)) (Ldeph d m) a b
        = (if a = m \<and> b = m then of_real (d m) else 0)"
      using m by (intro dag_Ldeph_Ldeph d0, simp)
    have m0: "m \<noteq> 0" using m by simp
    show "dissip n (Ldeph d m) rho j 0 = - (1/2) * (if j = m then of_real (d m) * rho j 0 else 0)"
      by (rule dissip_vac[where w = "of_real (d m)" and m = m, OF K jump_deph[OF m0] m0 jn])
  qed
  have sr: "(\<Sum>m\<in>{1..n}. dissip n (Lrel r m) rho j 0) = - (1/2) * of_real (r j) * rho j 0"
  proof -
    have "(\<Sum>m\<in>{1..n}. dissip n (Lrel r m) rho j 0)
        = (\<Sum>m\<in>{1..n}. - (1/2) * (if j = m then of_real (r m) * rho j 0 else 0))"
      by (rule sum.cong[OF refl rel])
    also have "\<dots> = (\<Sum>m\<in>{1..n}. if j = m then - (1/2) * (of_real (r m) * rho j 0) else 0)"
      by (rule sum.cong, simp_all)
    also have "\<dots> = - (1/2) * (of_real (r j) * rho j 0)"
      using j1 jn by (simp only: sum.delta'[OF finite_atLeastAtMost] atLeastAtMost_iff, simp)
    finally show ?thesis by simp
  qed
  have sd: "(\<Sum>m\<in>{1..n}. dissip n (Ldeph d m) rho j 0) = - (1/2) * of_real (d j) * rho j 0"
  proof -
    have "(\<Sum>m\<in>{1..n}. dissip n (Ldeph d m) rho j 0)
        = (\<Sum>m\<in>{1..n}. - (1/2) * (if j = m then of_real (d m) * rho j 0 else 0))"
      by (rule sum.cong[OF refl dep])
    also have "\<dots> = (\<Sum>m\<in>{1..n}. if j = m then - (1/2) * (of_real (d m) * rho j 0) else 0)"
      by (rule sum.cong, simp_all)
    also have "\<dots> = - (1/2) * (of_real (d j) * rho j 0)"
      using j1 jn by (simp only: sum.delta'[OF finite_atLeastAtMost] atLeastAtMost_iff, simp)
    finally show ?thesis by simp
  qed
  show ?thesis
    unfolding gen_def Gam_def
    by (simp only: ham1 ham2 sr sd of_real_add) (simp add: algebra_simps)
qed

section \<open>2. The no-jump form\<close>

theorem nojump_form:
  assumes H0: "\<And>k. H k 0 = 0"
    and r0: "\<And>j. r j \<ge> 0" and d0: "\<And>j. d j \<ge> 0"
    and j1: "1 \<le> j" and jn: "j \<le> n"
  shows "2 * gen n H r d rho j 0
    = - \<i> * (\<Sum>k\<in>{1..n}. (H j k - (\<i>/2) * of_real (Gam r d j) * (if j = k then 1 else 0))
                             * (2 * rho k 0))"
proof -
  have h: "\<And>k. k \<in> {1..n} \<Longrightarrow>
      (H j k - (\<i>/2) * of_real (Gam r d j) * (if j = k then 1 else 0)) * (2 * rho k 0)
      = 2 * (H j k * rho k 0) - \<i> * of_real (Gam r d j) * (if j = k then rho k 0 else 0)"
    by (auto simp add: algebra_simps)
  have "(\<Sum>k\<in>{1..n}. (H j k - (\<i>/2) * of_real (Gam r d j) * (if j = k then 1 else 0)) * (2 * rho k 0))
      = (\<Sum>k\<in>{1..n}. 2 * (H j k * rho k 0)
            - \<i> * of_real (Gam r d j) * (if j = k then rho k 0 else 0))"
    by (rule sum.cong[OF refl h])
  also have "\<dots> = 2 * (\<Sum>k\<in>{1..n}. H j k * rho k 0)
      - \<i> * of_real (Gam r d j) * rho j 0"
  proof -
    have a: "(\<Sum>k\<in>{1..n}. \<i> * of_real (Gam r d j) * (if j = k then rho k 0 else 0))
        = \<i> * of_real (Gam r d j) * rho j 0"
    proof -
      have "(\<Sum>k\<in>{1..n}. \<i> * of_real (Gam r d j) * (if j = k then rho k 0 else 0))
          = (\<Sum>k\<in>{1..n}. if j = k then \<i> * of_real (Gam r d j) * rho k 0 else 0)"
        by (rule sum.cong, simp_all)
      also have "\<dots> = \<i> * of_real (Gam r d j) * rho j 0"
        using j1 jn by (simp only: sum.delta'[OF finite_atLeastAtMost] atLeastAtMost_iff, simp)
      finally show ?thesis .
    qed
    show ?thesis
      by (simp only: sum_subtractf sum_distrib_left a)
  qed
  finally have e: "(\<Sum>k\<in>{1..n}. (H j k - (\<i>/2) * of_real (Gam r d j) * (if j = k then 1 else 0))
      * (2 * rho k 0)) = 2 * (\<Sum>k\<in>{1..n}. H j k * rho k 0) - \<i> * of_real (Gam r d j) * rho j 0" .
  have g: "gen n H r d rho j 0
      = - \<i> * (\<Sum>k\<in>{1..n}. H j k * rho k 0) - (1/2) * of_real (Gam r d j) * rho j 0"
    by (rule vacuum_coherence_generator[where H = H and r = r and d = d and j = j and n = n
        and rho = rho, OF H0 r0 d0 j1 jn])
  show ?thesis
    by (simp only: e g) (simp add: algebra_simps)
qed

section \<open>3. The relaxation and dephasing rates\<close>

theorem gamma_T2:
  fixes T1 T2 :: real
  assumes "T1 > 0" "T2 > 0"
  shows "1 / T1 + 2 * (1 / T2 - 1 / (2 * T1)) = 2 / T2"
  using assms by (simp add: field_simps)

end
