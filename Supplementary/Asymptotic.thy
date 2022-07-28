section\<open>Asymptotic Behavior\<close>

theory Asymptotic
  imports Complex_Main
    "HOL-Eisbach.Eisbach"
begin

text\<open>@{cite \<open>ch.~12.2\<close> hopcroftAutomata1979} uses the finite control in Lemma 12.3
  to make the jump from almost everywhere to everywhere:

  ``We say that a statement with parameter \<open>n\<close> is true \<^emph>\<open>almost everywhere\<close> (a.e.) if it
  is true for all but a finite number of values of \<open>n\<close>. We say a statement is true infinitely
  often (i.o.) if it is true for an infinite number of \<open>n\<close>'s. Note that both a statement and
  its negation may be true i.o.''

  We use the existing \<^const>\<open>Alm_all\<close> (\<open>\<forall>\<^sub>\<infinity> x. P x\<close>/\<open>MOST x. P x\<close>, ``for (almost all|almost every|most) x, ...'');
  see @{thm eventually_cofinite}.
  Note that the notion of \<^emph>\<open>almost everywhere\<close> is only sensible for non-\<^class>\<open>finite\<close> types.\<close>

lemma eventually_disj: "eventually P F \<or> eventually Q F \<Longrightarrow> eventually (\<lambda>x. P x \<or> Q x) F"
  by (elim disjE eventually_mono) auto


subsection\<open>Sufficiently Large\<close>

text\<open>Equivalence of \<^emph>\<open>for sufficiently large\<close> definitions as simple and general rewrite rule.
  Note that this only works in types with \<^class>\<open>no_top\<close> (@{thm gt_ex}),
  since for types with \<^class>\<open>order_top\<close>, \<^term>\<open>\<exists>n\<^sub>0. \<forall>n>n\<^sub>0. P n\<close> would trivially hold
  for \<^term>\<open>P = {}\<close> (\<^term>\<open>\<nexists>n. P n\<close>).\<close>

(*
abbreviation sufficiently_large (binder "sl " 20)
   where "sl n. P n \<equiv> \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n"
*)

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
  assumes "\<forall>\<^sub>\<infinity>n. P n"
  shows "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n"
proof -
  from assms have "P n" if "n > Max {n. \<not> P n}" for n
    using that
    unfolding eventually_cofinite using Max_gr_iff by blast
  then show "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n" by (blast intro: suff_large_gt_imp_ge)
qed

lemma suff_large_ae:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n"
  shows "\<forall>\<^sub>\<infinity>n. P n"
proof -
  from assms obtain n\<^sub>0 where *: "\<forall>n\<ge>n\<^sub>0. P n" by blast
  then have "{n. \<not> P n} \<subseteq> {n. n < n\<^sub>0}" using linorder_le_less_linear by blast
  then show "\<forall>\<^sub>\<infinity>n. P n" unfolding eventually_cofinite
    using finite_Collect_less_nat rev_finite_subset by blast
qed

lemma ae_suff_large_iff[iff]:
  fixes P :: "nat \<Rightarrow> bool"
  shows "(\<forall>\<^sub>\<infinity>n. P n) \<longleftrightarrow> (\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n)"
  using ae_suff_large and suff_large_ae by (rule iffI)

lemma ae_suff_largeI:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "\<And>n. n\<ge>n\<^sub>0 \<Longrightarrow> P n"
  shows "\<forall>\<^sub>\<infinity>n. P n"
  unfolding ae_suff_large_iff using assms by blast


method ae_intro uses add =
  insert add,
  (fold ae_suff_large_iff)?,
  (elim eventually_rev_mp)?,
  intro ae_suff_largeI impI

text\<open>To solve goals like \<open>\<lbrakk>\<forall>\<^sub>\<infinity>n. A n; \<forall>\<^sub>\<infinity>n. B n; ...\<rbrakk> \<Longrightarrow> \<forall>\<^sub>\<infinity>n. P n\<close>, where \<open>n :: nat\<close>,
  apply @{method ae_intro}, then prove the resulting goal
  of the form \<open>\<And>n. \<lbrakk>n\<ge>n\<^sub>0; A n; B n; ...\<rbrakk> \<Longrightarrow> P n\<close>.
  The additional premise \<open>n\<ge>n\<^sub>0\<close> allows specifying an arbitrary minimum,
  as many lemmas require proving \<open>n>0\<close> or similar.\<close>


subsection\<open>Asymptotic Domination\<close>

lemma dominates_ae_helper:
  fixes c :: real
  assumes "c > 0"
    and "T n \<noteq> 0"
  shows "c * \<bar>t n\<bar> < \<bar>T n\<bar> \<longleftrightarrow> \<bar>t n / T n\<bar> < 1/c"
proof -
  have "c * \<bar>t n\<bar> < \<bar>T n\<bar> \<longleftrightarrow> \<bar>t n\<bar> < \<bar>T n\<bar> / c"
    unfolding pos_less_divide_eq[OF \<open>c > 0\<close>] by argo
  also have "... \<longleftrightarrow> \<bar>t n\<bar> < \<bar>T n\<bar> * (1/c)" by argo
  also from \<open>T n \<noteq> 0\<close> have "... \<longleftrightarrow> \<bar>t n / T n\<bar> < 1/c"
    unfolding abs_divide by (subst pos_divide_less_eq) (simp, argo)
  finally show ?thesis .
qed

lemma dominates_ae:
  fixes T t :: "nat \<Rightarrow> real" and c :: real
  assumes "(\<lambda>n. t n / T n) \<longlonglongrightarrow> 0"
    and "\<forall>\<^sub>\<infinity>n. T n \<noteq> 0"
    and "c > 0"
  shows "\<forall>\<^sub>\<infinity>n. c * \<bar>t n\<bar> < \<bar>T n\<bar>"
proof -
  let ?r = "1/c"
  from \<open>c > 0\<close> have "?r > 0" by simp
  with \<open>(\<lambda>n. t n / T n) \<longlonglongrightarrow> 0\<close> have "\<forall>\<^sub>\<infinity>n. \<bar>t n / T n\<bar> < ?r"
    unfolding lim_sequentially dist_real_def diff_0_right by blast
  with \<open>\<forall>\<^sub>\<infinity>n. T n \<noteq> 0\<close> show "\<forall>\<^sub>\<infinity>n. c * \<bar>t n\<bar> < \<bar>T n\<bar>"
  proof (ae_intro)
    fix n
    assume "\<bar>t n / T n\<bar> < ?r" "T n \<noteq> 0"
    with \<open>c > 0\<close> show"c * \<bar>t n\<bar> < \<bar>T n\<bar>" by (subst dominates_ae_helper)
  qed
qed

lemma ae_dominates:
  fixes T t :: "nat \<Rightarrow> real" and c :: real
  assumes "\<And>c. \<forall>\<^sub>\<infinity>n. c * \<bar>t n\<bar> < \<bar>T n\<bar>"
  shows "(\<lambda>n. t n / T n) \<longlonglongrightarrow> 0"
proof -
  have "\<forall>\<^sub>\<infinity>n. \<bar>t n / T n\<bar> < r" if "r > 0" for r
  proof (ae_intro add: \<open>\<forall>\<^sub>\<infinity>n. (1/r) * \<bar>t n\<bar> < \<bar>T n\<bar>\<close>)
    from \<open>r > 0\<close> have "1/r > 0" by simp
    fix n
    assume "(1/r) * \<bar>t n\<bar> < \<bar>T n\<bar>"
    show "\<bar>t n / T n\<bar> < r"
    proof (cases "T n = 0")
      assume "T n = 0"
      with \<open>r > 0\<close> show ?thesis by simp
    next
      assume "T n \<noteq> 0"
      with \<open>(1/r) * \<bar>t n\<bar> < \<bar>T n\<bar>\<close> and \<open>1/r > 0\<close> have "\<bar>t n / T n\<bar> < 1/(1/r)"
        by (subst (asm) dominates_ae_helper)
      also have "... = r" by simp
      finally show ?thesis .
    qed
  qed
  then show "(\<lambda>n. t n / T n) \<longlonglongrightarrow> 0"
    unfolding lim_sequentially dist_real_def diff_0_right by blast
qed

lemma dominates_altdef:
  fixes T t :: "nat \<Rightarrow> real"
  assumes "\<forall>\<^sub>\<infinity>n. T n \<noteq> 0"
  shows "((\<lambda>n. t n / T n) \<longlonglongrightarrow> 0) \<longleftrightarrow> (\<forall>c>0. \<forall>\<^sub>\<infinity>n. c * \<bar>t n\<bar> < \<bar>T n\<bar>)"
proof
  assume "(\<lambda>n. t n / T n) \<longlonglongrightarrow> 0"
  then show "\<forall>c>0. \<forall>\<^sub>\<infinity>n. c * \<bar>t n\<bar> < \<bar>T n\<bar>" using assms by (intro allI impI dominates_ae)
next
  assume asm: "\<forall>c>0. \<forall>\<^sub>\<infinity>n. c * \<bar>t n\<bar> < \<bar>T n\<bar>"
  show "(\<lambda>n. t n / T n) \<longlonglongrightarrow> 0"
  proof (intro ae_dominates)
    fix c
    show "\<forall>\<^sub>\<infinity>n. c * \<bar>t n\<bar> < \<bar>T n\<bar>"
    proof (cases "c > 0")
      assume "c > 0"
      with asm show ?thesis by blast
    next
      assume "\<not> c > 0" hence "c \<le> 0" by simp
      from \<open>\<forall>\<^sub>\<infinity>n. T n \<noteq> 0\<close> show ?thesis
      proof (ae_intro)
        fix n assume "T n \<noteq> 0"
        from \<open>c \<le> 0\<close> have "c * \<bar>t n\<bar> \<le> 0" by (intro mult_nonneg_nonpos2) auto
        also from \<open>T n \<noteq> 0\<close> have "0 < \<bar>T n\<bar>" by simp
        finally show "c * \<bar>t n\<bar> < \<bar>T n\<bar>" .
      qed
    qed
  qed
qed

lemma dominates_mono:
  fixes T t :: "nat \<Rightarrow> real"
  assumes "(\<lambda>n. f n / T n) \<longlonglongrightarrow> 0"
    and "\<forall>\<^sub>\<infinity>n. T n \<noteq> 0"
    and "\<forall>\<^sub>\<infinity>n. \<bar>g n\<bar> \<le> \<bar>f n\<bar>"
  shows "(\<lambda>n. g n / T n) \<longlonglongrightarrow> 0"
proof -
  note * = dominates_altdef[OF \<open>\<forall>\<^sub>\<infinity>n. T n \<noteq> 0\<close>]

  show "(\<lambda>n. g n / T n) \<longlonglongrightarrow> 0" unfolding *
  proof (intro allI impI)
    fix c :: real
    assume "c > 0"
    with \<open>(\<lambda>n. f n / T n) \<longlonglongrightarrow> 0\<close> have "\<forall>\<^sub>\<infinity>n. c * \<bar>f n\<bar> < \<bar>T n\<bar>" unfolding * by blast
    with \<open>\<forall>\<^sub>\<infinity>n. \<bar>g n\<bar> \<le> \<bar>f n\<bar>\<close> show "\<forall>\<^sub>\<infinity>n. c * \<bar>g n\<bar> < \<bar>T n\<bar>"
    proof (ae_intro)
      fix n :: nat
      assume "\<bar>g n\<bar> \<le> \<bar>f n\<bar>"
      moreover from \<open>c > 0\<close> have "c \<ge> 0" by simp
      ultimately have "c * \<bar>g n\<bar> \<le> c * \<bar>f n\<bar>" by (rule mult_left_mono)
      also assume "... < \<bar>T n\<bar>"
      finally show "c * \<bar>g n\<bar> < \<bar>T n\<bar>" .
    qed
  qed
qed

lemma superlinearE:
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

lemma superlinearE':
  fixes T :: "nat \<Rightarrow> real" and c :: real
  assumes "\<forall>N. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n)/n \<ge> N"
  shows "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. T(n) \<ge> c*n"
  using assms by (elim superlinearE) blast


end
