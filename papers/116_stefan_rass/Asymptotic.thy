section\<open>Asymptotic Behavior\<close>

theory Asymptotic
  imports Complex_Main "HOL-Library.BigO"
begin

text\<open>@{cite \<open>ch.~12.2\<close> hopcroftAutomata1979} uses the finite control in Lemma 12.3
  to make the jump from almost everywhere to everywhere:

  ``We say that a statement with parameter \<open>n\<close> is true \<^emph>\<open>almost everywhere\<close> (a.e.) if it
  is true for all but a finite number of values of \<open>n\<close>. We say a statement is true infinitely
  often (i.o.) if it is true for an infinite number of \<open>n\<close>'s. Note that both a statement and
  its negation may be true i.o.''

  We introduce the \<^emph>\<open>binder\<close> notation \<open>ae x. P x\<close> (``for almost every x'').\<close>

definition almost_everywhere :: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "ae " 20)
  where ae_def[simp]: "ae x. P x \<equiv> finite {x. \<not> P x}"

lemma ae_everyI: "(\<And>x. P x) \<Longrightarrow> (ae x. P x)" by simp


lemma ae_conj_iff: "(ae x. P x \<and> Q x) \<longleftrightarrow> (ae x. P x) \<and> (ae x. Q x)"
  unfolding ae_def de_Morgan_conj Collect_disj_eq by blast

lemma ae_conjI:
  assumes "ae x. P x" and "ae x. Q x"
  shows "ae x. P x \<and> Q x"
  unfolding ae_conj_iff using assms ..

lemma ae_mono2:
  assumes "ae x. P x"
    and "ae x. P x \<longrightarrow> Q x"
  shows "ae x. Q x"
proof -
  have "{x. \<not> Q x} \<subseteq> {x. \<not> (P x \<and> (P x \<longrightarrow> Q x))}" by blast
  moreover from assms have "ae x. P x \<and> (P x \<longrightarrow> Q x)" by (rule ae_conjI)
  ultimately show "ae x. Q x" unfolding ae_def by (rule finite_subset)
qed

lemma ae_mono:
  assumes "ae x. P x"
    and "\<And>x. P x \<Longrightarrow> Q x"
  shows "ae x. Q x"
  using assms(1) by (rule ae_mono2) (use assms(2) in simp)


lemma ae_disj: "(ae x. P x) \<or> (ae x. Q x) \<Longrightarrow> ae x. P x \<or> Q x"
  by auto


subsection\<open>Sufficiently Large\<close>

text\<open>Equivalence of \<^emph>\<open>for sufficiently large\<close> definitions as simple and general rewrite rule.
  Note that this only works in types with \<^class>\<open>no_top\<close> (@{thm gt_ex}),
  since for types with \<^class>\<open>order_top\<close>, \<^term>\<open>\<exists>n\<^sub>0. \<forall>n>n\<^sub>0. P n\<close> would trivially hold
  for \<^term>\<open>P = {}\<close> (\<^term>\<open>\<nexists>n. P n\<close>).\<close>

abbreviation sufficiently_large (binder "sl " 20)
  where "sl n. P n \<equiv> \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n"

lemma suff_large_ge_imp_gt:
  fixes P :: "'a::{preorder} \<Rightarrow> bool"
  assumes "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n"
  shows "\<exists>n\<^sub>0. \<forall>n>n\<^sub>0. P n"
proof -
  from assms obtain n\<^sub>0 where "\<forall>n\<ge>n\<^sub>0. P n" ..
  then have "\<forall>n>n\<^sub>0. P n" using order_less_imp_le by blast
  then show ?thesis ..
qed

lemma suff_large_gt_imp_ge:
  fixes P :: "'a::{no_top} \<Rightarrow> bool"
  assumes "\<exists>n\<^sub>0. \<forall>n>n\<^sub>0. P n"
  shows "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n"
proof -
  from assms obtain n\<^sub>0 where "\<forall>n>n\<^sub>0. P n" ..
  from gt_ex obtain n\<^sub>0' where "n\<^sub>0' > n\<^sub>0" ..
  with \<open>\<forall>n>n\<^sub>0. P n\<close> have "\<forall>n\<ge>n\<^sub>0'. P n" by simp
  then show ?thesis ..
qed

lemma suff_large_iff:
  fixes P :: "'a::{no_top} \<Rightarrow> bool"
  shows "(\<exists>n\<^sub>0. \<forall>n>n\<^sub>0. P n) \<longleftrightarrow> (\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n)"
  using suff_large_gt_imp_ge and suff_large_ge_imp_gt by (rule iffI)


text\<open>Relationship of \<^emph>\<open>sufficiently large\<close> and \<^emph>\<open>almost everywhere\<close>\<close>

lemma ae_suff_large: 
  fixes P :: "'a::{linorder, no_top} \<Rightarrow> bool"
  assumes "ae n. P n"
  shows "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n"
proof -
  from assms have "P n" if "n > Max {n. \<not> P n}" for n
    using that
    unfolding ae_def using Max_gr_iff by blast
  then show "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n" by (blast intro: suff_large_gt_imp_ge)
qed

lemma suff_large_ae:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n"
  shows "ae n. P n"
proof -
  from assms obtain n\<^sub>0 where *: "\<forall>n\<ge>n\<^sub>0. P n" by blast
  then have "{n. \<not> P n} \<subseteq> {n. n < n\<^sub>0}" using linorder_le_less_linear by blast
  then show "ae n. P n" unfolding ae_def
    using finite_Collect_less_nat rev_finite_subset by blast 
qed

lemma ae_suff_large_iff:
  fixes P :: "nat \<Rightarrow> bool"
  shows "(ae x. P x) \<longleftrightarrow> (\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n)"
  using ae_suff_large and suff_large_ae by (rule iffI)


subsection\<open>Asymptotic Domination\<close>

(* TODO unify definitions *)

lemma dominates_altdef:
  fixes T t :: "nat \<Rightarrow> real"
  assumes "\<And>n. T n \<noteq> 0"
  shows "((\<lambda>n. t n / T n) \<longlonglongrightarrow> 0) \<longleftrightarrow> (\<forall>c>0. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. c * \<bar>t n\<bar> < \<bar>T n\<bar>)"
proof -
  have *: "c * \<bar>t n\<bar> < \<bar>T n\<bar> \<longleftrightarrow> \<bar>t n / T n\<bar> < 1/c" if "c > 0" for c :: real and n
  proof -
    have "c * \<bar>t n\<bar> < \<bar>T n\<bar> \<longleftrightarrow> \<bar>t n\<bar> < \<bar>T n\<bar> / c"
      unfolding pos_less_divide_eq[OF \<open>c > 0\<close>] by argo
    also have "... \<longleftrightarrow> \<bar>t n\<bar> < \<bar>T n\<bar> * (1/c)" by argo
    also from \<open>T n \<noteq> 0\<close> have "... \<longleftrightarrow> \<bar>t n / T n\<bar> < 1/c"
      unfolding abs_divide by (subst pos_divide_less_eq) (simp, argo)
    finally show ?thesis .
  qed
  
  have "(\<forall>r>0. \<exists>no. \<forall>n\<ge>no. \<bar>t n / T n\<bar> < r) = (\<forall>c>0. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. c * \<bar>t n\<bar> < \<bar>T n\<bar>)"
  proof (intro iffI allI impI; elim allE impE)
    fix c :: real
    assume "c > 0" thus "1/c > 0" by simp
    assume "\<exists>no. \<forall>n\<ge>no. \<bar>t n / T n\<bar> < 1/c"
    with \<open>c > 0\<close> show "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. c * \<bar>t n\<bar> < \<bar>T n\<bar>" using * by blast
  next
    fix r :: real
    assume "r > 0" thus "1/r > 0" by simp
    assume "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. 1/r * \<bar>t n\<bar> < \<bar>T n\<bar>"
    with \<open>1/r > 0\<close> have "\<exists>no. \<forall>n\<ge>no. \<bar>t n / T n\<bar> < 1/(1/r)" using * by blast
    then show "\<exists>no. \<forall>n\<ge>no. \<bar>t n / T n\<bar> < r" by simp
  qed
  then show ?thesis unfolding LIMSEQ_def dist_real_def diff_0_right .
qed

lemma dominatesE:
  fixes T :: "nat \<Rightarrow> real" and c :: real
  assumes "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n)/n \<ge> N"
  obtains n\<^sub>0 where "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> T(n) \<ge> c*n"
proof -
  from assms obtain n\<^sub>0 where n\<^sub>0: "T(n)/n \<ge> c" if "n \<ge> n\<^sub>0" for n by blast

  then have "T(n) \<ge> c*n" if "n \<ge> Suc n\<^sub>0" (is "n \<ge> ?n") for n
  proof -
    from \<open>n \<ge> Suc n\<^sub>0\<close> have "n \<ge> n\<^sub>0" by (fact Suc_leD)
    with n\<^sub>0 have "T(n)/n \<ge> c" .
    moreover from \<open>n \<ge> Suc n\<^sub>0\<close> have "real n > 0" by simp
    ultimately show "T(n) \<ge> c*n" by (subst (asm) pos_le_divide_eq)
  qed
  then show ?thesis by (rule that)
qed

lemma dominatesE':
  fixes T :: "nat \<Rightarrow> real" and c :: real
  assumes "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n)/n \<ge> N"
  shows "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n) \<ge> c*n"
  using assms by (elim dominatesE) blast


end
