theory Misc
  imports Main
begin

lemma inj_imp_inj_on: "inj f \<Longrightarrow> inj_on f A" by (simp add: inj_on_def)

(* Suppl_Set ? *)
lemma image_Collect_compose: "f ` {g x | x. P x} = {f (g x) | x. P x}" by blast

lemma finite_imp_inj_to_nat_fix_one:
  fixes A::"'a set" and x::'a and y::nat
  assumes "finite A"
  shows "\<exists>g. inj_on g A \<and> g x = y"
proof -
  from finite_imp_inj_to_nat_seg[OF assms]
  obtain f n where "f ` A = {..<n::nat}" and "inj_on f A" by auto

  define g where "g = (\<lambda>x. f x + y + 1)(x := y)"
  from g_def have 1: "g x' = y \<Longrightarrow> x' = x" for x'
    by (cases "x' = x") simp+
  from g_def have 2: "a \<in> A \<Longrightarrow> a \<noteq> x \<Longrightarrow> g a = f a + y + 1" for a
    by simp

  have "inj_on g A" proof (intro inj_onI)
    fix a1 a2
    assume "a1 \<in> A" "a2 \<in> A" "g a1 = g a2"
    thus "a1 = a2" proof (cases "a1 = x")
      case True
      then have "g a1 = y" unfolding g_def by simp
      with 1[of a2] \<open>a1 = x\<close> \<open>g a1 = g a2\<close> show "a1 = a2" by simp
    next
      case False
      have "a2 \<noteq> x" proof (rule ccontr)
        assume "\<not> a2 \<noteq> x"
        hence "g a2 = y" unfolding g_def by simp
        with \<open>g a1 = g a2\<close> have "a1 = x" using 1[of a1] by simp
        thus False using \<open>a1 \<noteq> x\<close> by simp
      qed
      with \<open>a2 \<in> A\<close> 2 have "g a2 = f a2 + y + 1" by simp
      moreover have "g a1 = f a1 + y + 1" using \<open>a1 \<noteq> x\<close> \<open>a1 \<in> A\<close> 2 by simp
      ultimately have "f a1 = f a2" using \<open>g a1 = g a2\<close> by force
      thus "a1 = a2" using \<open>inj_on f A\<close> \<open>a1 \<in> A\<close> \<open>a2 \<in> A\<close> by (elim inj_onD)
    qed
  qed
  moreover have "g x = y" unfolding g_def fun_upd_same ..
  ultimately show ?thesis by blast
qed

(* Suppl_Orderings ? *)
lemma nat_strict_mono_greatest:
  fixes f::"nat \<Rightarrow> nat" and N::nat
  assumes "strict_mono f" "f 0 \<le> N"
  obtains n where "f n \<le> N" and "\<forall>m. f m \<le> N \<longrightarrow> m \<le> n"
proof -
  define M where "M \<equiv> {m. f m \<le> N}"
  define n where "n = Max M"

  from \<open>strict_mono f\<close> have "\<And>n. n \<le> f n" by (rule strict_mono_imp_increasing)
  hence "finite M" using M_def finite_less_ub by simp
  moreover from M_def \<open>f 0 \<le> N\<close> have "M \<noteq> {}" by auto
  ultimately have "n \<in> M" unfolding n_def using Max_in[of M] by simp

  then have "f n \<le> N" using n_def M_def by simp
  moreover have "\<forall>m. f m \<le> N \<longrightarrow> m \<le> n"
    using Max_ge \<open>finite M\<close> n_def M_def by blast
  ultimately show thesis using that by simp
qed

lemma max_cases:
  assumes "P a"
    and "P b"
  shows "P (max a b)"
  using assms unfolding max_def by simp

lemma max_nat: "max a b = a + (b - a)" for a b :: nat
  using nat_le_linear[of a b] by fastforce

lemma fold_max_triv: "fold max xs x \<ge> x" for x :: "'a :: linorder" and xs
  by (fold Max.set_eq_fold) simp

(* Suppl_Nat.thy ? *)
lemma funpow_fixpoint: "f x = x \<Longrightarrow> (f^^n) x = x"
  by (induction n) simp_all

end
