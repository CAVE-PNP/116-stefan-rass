section\<open>Asymptotic Behavior\<close>

theory Asymptotic
  imports Complex_Main Lists
    "HOL-Eisbach.Eisbach"
    "Intro_Dest_Elim.IHOL_IDE"
begin

subsection\<open>Almost Everywhere\<close>

text\<open>@{cite \<open>ch.~12.2\<close> hopcroftAutomata1979} uses the finite control in Lemma 12.3
  to make the jump from almost everywhere to everywhere:

  ``We say that a statement with parameter \<open>n\<close> is true \<^emph>\<open>almost everywhere\<close> (a.e.) if it
  is true for all but a finite number of values of \<open>n\<close>. We say a statement is true infinitely
  often (i.o.) if it is true for an infinite number of \<open>n\<close>'s. Note that both a statement and
  its negation may be true i.o.''

  We use the existing \<^const>\<open>Alm_all\<close> (\<^term>\<open>\<forall>\<^sub>\<infinity>x. P x\<close>/\<^term>\<open>MOST x. P x\<close>,
  ``for (almost all|almost every|most) x, ...''); see @{thm eventually_cofinite}
  (see also the analogous \<^const>\<open>Inf_many\<close>; \<^term>\<open>\<exists>\<^sub>\<infinity>x. P x\<close>/\<^term>\<open>INFM x. P x\<close>).
  Note that the notion of \<^emph>\<open>almost everywhere\<close> is only sensible for non-\<^class>\<open>finite\<close> types.\<close>

lemma eventually_disj[intro]: "eventually P F \<or> eventually Q F \<Longrightarrow> eventually (\<lambda>x. P x \<or> Q x) F"
  by (elim disjE eventually_mono) blast+

declare eventually_conj_iff[iff]
declare eventually_rev_mp[elim]
declare eventuallyI[intro?]


subsubsection\<open>Bounded almost everywhere\<close>

text\<open>Syntactic sugar for \<^emph>\<open>bounded almost everywhere\<close>: \<open>\<forall>\<^sub>\<infinity>x\<in>A. P x := \<forall>\<^sub>\<infinity>x. x \<in> A \<longrightarrow> P x\<close>.
  Analogous to \<^emph>\<open>bounded all\<close> (\<^const>\<open>Ball\<close>) and its notation \<^term>\<open>\<forall>x\<in>A. P x\<close>.\<close>

abbreviation Alm_ball :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Alm_ball A P \<equiv> \<forall>\<^sub>\<infinity>x. x \<in> A \<longrightarrow> P x"
syntax
  "_Alm_ball" :: "pttrn \<Rightarrow> 's set \<Rightarrow> bool \<Rightarrow> bool"   ("(3\<forall>\<^sub>\<infinity>_/\<in>_./ _)" [0, 0, 10] 10)
translations
  "\<forall>\<^sub>\<infinity>x\<in>A. P" \<rightleftharpoons> "CONST Alm_ball A (\<lambda>x. P)"
print_translation\<open>[
  Syntax_Trans.preserve_binder_abs2_tr' \<^const_syntax>\<open>Alm_ball\<close> \<^syntax_const>\<open>_Alm_ball\<close>
]\<close> \<comment> \<open>to avoid eta-contraction of body (otherwise, \<^term>\<open>\<forall>\<^sub>\<infinity>x\<in>A. P x\<close> will be printed as \<^term>\<open>Alm_ball A P\<close>)\<close>


subsubsection\<open>Over the Naturals: For Sufficiently Large \<open>n\<close>\<close>

text\<open>\<^emph>\<open>almost everywhere\<close> statements over the natural numbers are often
  equivalently expressed as \<^emph>\<open>for sufficiently large \<open>n\<close>\<close> (\<^term>\<open>\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n\<close>).
  We introduce a proof method to simplify such statements.\<close>

lemma Alm_all_nat_altdef:
  fixes P :: "nat \<Rightarrow> bool"
  shows "(\<forall>\<^sub>\<infinity>x. P x) \<longleftrightarrow> (\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n)"
  unfolding cofinite_eq_sequentially by (fact eventually_sequentially)

mk_ide Alm_all_nat_altdef |intro Alm_all_natI[intro]| |dest Alm_all_natD[dest]|

lemma Alm_all_natI': "(\<And>n::nat. n\<ge>n\<^sub>0 \<Longrightarrow> P n) \<Longrightarrow> \<forall>\<^sub>\<infinity>n. P n"
  using Alm_all_nat_altdef by blast

lemma Alm_all_natE':
  assumes "\<forall>\<^sub>\<infinity>n. P n"
  obtains n\<^sub>0 where "\<And>n::nat. n\<ge>n\<^sub>0 \<Longrightarrow> P n"
  using assms unfolding Alm_all_nat_altdef by blast

text\<open>To solve goals like \<open>\<lbrakk>\<forall>\<^sub>\<infinity>n. P\<^sub>1 n; \<forall>\<^sub>\<infinity>n. P\<^sub>2 n; ...\<rbrakk> \<Longrightarrow> \<forall>\<^sub>\<infinity>n. Q n\<close>, where \<open>n :: nat\<close>,
  apply \<open>ae_nat_elim\<close>, then prove the resulting goal
  of the form \<open>\<And>n. \<lbrakk>n\<ge>n\<^sub>0; A n; B n; ...\<rbrakk> \<Longrightarrow> P n\<close>.
  The additional premise \<open>n\<ge>n\<^sub>0\<close> allows specifying an arbitrary minimum,
  as many lemmas require proving \<open>n>0\<close> or similar.
  The variant \<open>ae_nat_param_elim\<close> allows to fix \<open>n\<^sub>0\<close> in advance.

  Supply input facts via the parameter \<open>ae_nat_elim add: some_fact\<close>,
  or by chaining them into \<open>ae_nat_elim\<close>
  (this will leave them in the premises and lead to clutter after elimination, however).
  If no input facts are given, this is equivalent to just applying @{thm Alm_all_natI}.

  Note that this is somewhat similar to @{method eventually_elim},
  but tailored to statements over the naturals.
  Crucially, @{method eventually_elim} does not provide the additional premise \<open>n\<ge>n\<^sub>0\<close>.\<close>

method ae_nat_elim uses add =
  (intro eventually_subst)?,
  insert add,
  (fold Alm_all_nat_altdef)?,
  (elim eventually_rev_mp)?,
  intro Alm_all_natI' impI

method ae_nat_param_elim for n\<^sub>0 :: nat uses add =
  (intro eventually_subst)?,
  insert add,
  (fold Alm_all_nat_altdef)?,
  (elim eventually_rev_mp)?,
  intro Alm_all_natI'[where n\<^sub>0=n\<^sub>0] impI


text\<open>Equivalence of different \<^emph>\<open>sufficiently large\<close> definitions as simple and general rewrite rule.
  Note that this only works in types with \<^class>\<open>no_top\<close> (@{thm gt_ex}),
  since for types with \<^class>\<open>order_top\<close>, \<^term>\<open>\<exists>n\<^sub>0. \<forall>n>n\<^sub>0. P n\<close> would trivially hold
  for \<^term>\<open>P \<equiv> \<lambda>n. False\<close> (\<^term>\<open>\<nexists>n. P n\<close>).\<close>

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


subsubsection\<open>Over Languages\<close>

text\<open>Analogously to \<^emph>\<open>sufficiently large\<close> over the naturals,
  we introduce a proof method for \<^emph>\<open>almost everywhere\<close> statements over sets of words
  (constrained by a finite alphabet),
  based on the equivalence \<^term>\<open>(\<forall>\<^sub>\<infinity>w\<in>\<Sigma>*. P w) \<longleftrightarrow> (\<exists>l\<^sub>0. \<forall>w\<in>\<Sigma>*. length w \<ge> l\<^sub>0 \<longrightarrow> P w)\<close>
  (if \<^term>\<open>finite \<Sigma>\<close>).\<close>

lemma ae_word_lengthI:
  fixes P :: "'s list \<Rightarrow> bool" and \<Sigma> :: "'s set"
  assumes "finite \<Sigma>"
  assumes "\<And>w. w \<in> \<Sigma>* \<Longrightarrow> n \<le> length w \<Longrightarrow> P w"
  shows "\<forall>\<^sub>\<infinity>w\<in>\<Sigma>*. P w"
proof -
  define P' where "P' w \<equiv> w \<in> \<Sigma>* \<longrightarrow> P w" for w
  from assms(2) obtain n where n_def: "P' w" if "n \<le> length w" for w :: "'s list" unfolding P'_def by blast
  have "\<not> P' w \<longrightarrow> set w \<subseteq> \<Sigma> \<and> length w \<le> n" for w using n_def[of w] unfolding P'_def by force
  then have "{w. \<not> P' w} \<subseteq> {w. set w \<subseteq> \<Sigma> \<and> length w \<le> n}" by blast
  moreover from \<open>finite \<Sigma>\<close> have "finite {w. set w \<subseteq> \<Sigma> \<and> length w \<le> n}" by (fact finite_lists_length_le)
  ultimately show "\<forall>\<^sub>\<infinity>w. P' w" unfolding P'_def eventually_cofinite by (rule finite_subset)
qed

lemma ae_word_lengthE[elim?]:
  fixes P :: "'s list \<Rightarrow> bool" and \<Sigma> :: "'s set"
  defines "P' w \<equiv> w \<in> \<Sigma>* \<longrightarrow> P w"
  assumes "\<forall>\<^sub>\<infinity>w. P' w"
  obtains n where "\<And>w. w \<in> \<Sigma>* \<Longrightarrow> n \<le> length w \<Longrightarrow> P w"
proof (rule that, cases "{w. \<not> P' w} = {}")
  assume "{w. \<not> P' w} \<noteq> {}"
  define n where "n = Suc (Max (length ` {w. \<not> P' w}))"
  fix w assume "w \<in> \<Sigma>*" and "n \<le> length w"

  from \<open>\<forall>\<^sub>\<infinity>w. P' w\<close> have "finite {w. \<not> P' w}" unfolding eventually_cofinite .
  from \<open>length w \<ge> n\<close> have "length w > Max (length ` {w. \<not> P' w})"
    unfolding n_def by (fact Suc_le_lessD)
  then have "length w \<notin> length ` {w. \<not> P' w}"
    using \<open>{w. \<not> P' w} \<noteq> {}\<close> and \<open>finite {w. \<not> P' w}\<close> by (subst (asm) Max_less_iff) blast+
  then have "P' w" by blast
  with \<open>w \<in> \<Sigma>*\<close> show "P w" unfolding P'_def by blast
qed (use assms in blast)

lemma ae_word_length_iff:
  fixes P :: "'s list \<Rightarrow> bool"
  assumes "finite \<Sigma>"
  shows "(\<forall>\<^sub>\<infinity>w\<in>\<Sigma>*. P w) \<longleftrightarrow> (\<exists>n. \<forall>w\<in>\<Sigma>*. n \<le> length w \<longrightarrow> P w)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs" by (elim ae_word_lengthE) blast
next
  assume ?rhs
  then obtain n where "P w" if "w \<in> \<Sigma>*" and "n \<le> length w" for w by blast
  with \<open>finite \<Sigma>\<close> show ?lhs by (intro ae_word_lengthI)
qed

lemma ae_word_length_iff':
  assumes "finite \<Sigma>"
  shows "(\<forall>\<^sub>\<infinity>w\<in>\<Sigma>*. P w) \<longleftrightarrow> (\<forall>\<^sub>\<infinity>n. \<forall>w\<in>\<Sigma>*. length w = n \<longrightarrow> P w)"
  unfolding ae_word_length_iff[OF assms] Alm_all_nat_altdef by auto


lemma ae_word_rev_mpE: \<comment> \<open>analogous to @{thm eventually_rev_mp}, but does not produce duplicates of \<^term>\<open>w\<in>\<Sigma>*\<close>.\<close>
  assumes "\<forall>\<^sub>\<infinity>w\<in>\<Sigma>*. P w"
    and "\<forall>\<^sub>\<infinity>w\<in>\<Sigma>*. P w \<longrightarrow> Q w"
  shows "\<forall>\<^sub>\<infinity>w\<in>\<Sigma>*. Q w"
  using assms by (elim eventually_rev_mp) simp

method ae_words_elim =
  -, (* add chained facts as premises, required for match *)
  match conclusion in "\<forall>\<^sub>\<infinity>w\<in>\<Sigma>*. _ w" for \<Sigma> \<Rightarrow> \<open> (* fix the alphabet \<open>\<Sigma>\<close> *)
    match premises in fin[thin]: "finite \<Sigma>" \<Rightarrow> \<open>
      (unfold ae_word_length_iff[symmetric, OF fin])?, (* fold does not work with the symbolic \<open>fin\<close> *)
      (match premises in ae_assms[thin]: "\<forall>\<^sub>\<infinity>w\<in>\<Sigma>*. _ w" (multi)
                     and ex_assms[thin]: "\<exists>N. \<forall>n\<ge>N. _ n" (multi) \<Rightarrow> \<open>
        use ae_assms ex_assms[unfolded ae_word_length_iff[symmetric, OF fin]]
          in \<open>elim ae_word_rev_mpE\<close>
      \<close>)?,
      intro ae_word_lengthI[OF fin] impI
    \<close>
  \<close>


lemma ae_word_length_finite_iff:
  fixes P :: "'s::finite list \<Rightarrow> bool"
  shows "(\<forall>\<^sub>\<infinity>x. P x) \<longleftrightarrow> (\<exists>n. \<forall>w. n \<le> length w \<longrightarrow> P w)" (is "?lhs \<longleftrightarrow> ?rhs")
  using ae_word_length_iff[of UNIV P] by simp

lemma ae_word_length_finiteI:
  fixes P :: "'s::finite list \<Rightarrow> bool"
  assumes "\<And>w. n \<le> length w \<Longrightarrow> P w"
  shows "\<forall>\<^sub>\<infinity>x. P x"
  unfolding ae_word_length_finite_iff using assms by blast

lemma ae_word_length_finiteE[elim?]:
  fixes P :: "'s::finite list \<Rightarrow> bool"
  assumes "\<forall>\<^sub>\<infinity>x. P x"
  obtains n where "\<And>w. n \<le> length w \<Longrightarrow> P w"
  using assms unfolding ae_word_length_finite_iff by blast


subsection\<open>Asymptotic Domination\<close>

lemma dominates_helper:
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
  shows "\<forall>\<^sub>\<infinity>n. c * \<bar>t n\<bar> < \<bar>T n\<bar>"
proof cases
  assume [simp]: "c = 0"
  show ?thesis by (ae_nat_elim add: \<open>\<forall>\<^sub>\<infinity>n. T n \<noteq> 0\<close>) simp
next
  let ?r = "1/\<bar>c\<bar>"
  assume "c \<noteq> 0"
  then have "\<bar>c\<bar> > 0" by simp
  then have "?r > 0" by simp
  with \<open>(\<lambda>n. t n / T n) \<longlonglongrightarrow> 0\<close> have "\<forall>\<^sub>\<infinity>n. \<bar>t n / T n\<bar> < ?r"
    unfolding lim_sequentially dist_real_def diff_0_right by blast
  with \<open>\<forall>\<^sub>\<infinity>n. T n \<noteq> 0\<close> show "\<forall>\<^sub>\<infinity>n. c * \<bar>t n\<bar> < \<bar>T n\<bar>"
  proof ae_nat_elim
    fix n
    assume "\<bar>t n / T n\<bar> < ?r" and "T n \<noteq> 0"

    have "c * \<bar>t n\<bar> \<le> \<bar>c\<bar> * \<bar>t n\<bar>" using mult_right_mono abs_ge_self abs_ge_zero .
    also from \<open>\<bar>c\<bar> > 0\<close> and \<open>\<bar>t n / T n\<bar> < ?r\<close> and \<open>T n \<noteq> 0\<close> have "\<bar>c\<bar> * \<bar>t n\<bar> < \<bar>T n\<bar>"
      by (subst dominates_helper)
    finally show "c * \<bar>t n\<bar> < \<bar>T n\<bar>" .
  qed
qed

lemma ae_dominates:
  fixes T t :: "nat \<Rightarrow> real" and c :: real
  assumes "\<And>c. \<forall>\<^sub>\<infinity>n. c * \<bar>t n\<bar> < \<bar>T n\<bar>"
  shows "(\<lambda>n. t n / T n) \<longlonglongrightarrow> 0"
proof -
  have "\<forall>\<^sub>\<infinity>n. \<bar>t n / T n\<bar> < r" if "r > 0" for r
  proof (ae_nat_elim add: \<open>\<forall>\<^sub>\<infinity>n. (1/r) * \<bar>t n\<bar> < \<bar>T n\<bar>\<close>)
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
        by (subst (asm) dominates_helper)
      also have "... = r" by simp
      finally show ?thesis .
    qed
  qed
  then show "(\<lambda>n. t n / T n) \<longlonglongrightarrow> 0"
    unfolding lim_sequentially dist_real_def diff_0_right Alm_all_nat_altdef by blast
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
      proof ae_nat_elim
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
    proof ae_nat_elim
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
  assumes "\<And>N. \<forall>\<^sub>\<infinity>n. T(n)/n \<ge> N"
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
  assumes "\<And>N. \<forall>\<^sub>\<infinity>n. T(n)/n \<ge> N"
  shows "\<forall>\<^sub>\<infinity>n. T(n) \<ge> c*n"
  using assms by (elim superlinearE) blast


definition unbounded :: "('a :: linorder \<Rightarrow> 'b :: linorder) \<Rightarrow> bool"
  where "unbounded f \<equiv> \<forall>S. \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. S \<le> f n"

lemma unboundedD[dest]:
  assumes "unbounded f"
  obtains n0 where "\<And>n. n \<ge> n0 \<Longrightarrow> S \<le> f n"
  using assms unfolding unbounded_def by blast

(* TODO assess if \<open>HOL-Library.BigO\<close> save effort here. *)
definition superlinear :: "('a :: {linorder,semiring_1} \<Rightarrow> 'b :: {linorder,semiring_1}) \<Rightarrow> bool"
  where "superlinear f \<equiv> \<forall>C. \<forall>\<^sub>\<infinity>n. of_nat (C * n) \<le> f (of_nat n)"

lemma superlinear_altdef_lf: \<comment> \<open>for \<^typ>\<open>real\<close>\<close>
  fixes f :: "'a :: linordered_field \<Rightarrow> 'b :: linordered_field"
  shows "superlinear f \<longleftrightarrow> (\<forall>C. \<forall>\<^sub>\<infinity>n. (of_nat C) \<le> f (of_nat n) / (of_nat n))"
  unfolding superlinear_def of_nat_mult
  by (intro all_cong1, ae_nat_param_elim 1, intro pos_le_divide_eq[symmetric]) simp

lemma superlinear_altdef_nat:
  fixes f :: "nat \<Rightarrow> nat"
  shows "superlinear f \<longleftrightarrow> (\<forall>C. \<forall>\<^sub>\<infinity>n. C * n \<le> f n)"
  by (auto simp: superlinear_def)

lemma superlinear_altdef_nat':
  fixes f :: "nat \<Rightarrow> nat"
  shows "superlinear f \<longleftrightarrow> (\<forall>C. \<forall>\<^sub>\<infinity>n. C \<le> f n div n)"
  unfolding superlinear_altdef_nat
  by (intro all_cong1, ae_nat_param_elim 1, intro less_eq_div_iff_mult_less_eq[symmetric]) simp

lemma superlinear_of_nat[simp]:
  fixes f :: "nat \<Rightarrow> nat" and f' :: "nat \<Rightarrow> 'a :: linordered_nonzero_semiring"
  defines "f' x \<equiv> of_nat (f x)" (is "\<And>x. f' x \<equiv> ?of_nat (f x)")
  shows "superlinear f' = superlinear f"
  unfolding superlinear_def of_nat_id f'_def of_nat_le_iff ..

lemma superlinear_factor[simp]:
  fixes f :: "'a :: {linorder,semiring_1} \<Rightarrow> 'b :: floor_ceiling"
  assumes "c > 0"
  shows "superlinear (\<lambda>x. c * f x) \<longleftrightarrow> superlinear f"
  unfolding superlinear_def
proof (intro iffI allI; elim allE; ae_nat_elim)
  fix C n :: nat
  let ?C = "Suc C"
  assume "n \<ge> 1"

  from \<open>c > 0\<close> have "c * of_nat (C * n) \<le> c * of_nat (?C * n)" by simp
  also have "... \<le> of_nat (nat \<lceil>c\<rceil>) * of_nat (?C * n)"
  proof (subst mult_le_cancel_iff1)
    from \<open>c > 0\<close> and \<open>n \<ge> 1\<close> show "(0::'b) < of_nat (Suc C * n)"
      unfolding of_nat_0_less_iff by simp
    show "c \<le> of_nat (nat \<lceil>c\<rceil>)" by (fact of_nat_ceiling)
  qed
  also have "... \<le> of_nat (nat \<lceil>c\<rceil> * ?C * n)" unfolding of_nat_mult mult.assoc ..
  also assume "of_nat (nat \<lceil>c\<rceil> * ?C * n) \<le> c * f (of_nat n)"
  finally show "of_nat (C * n) \<le> f (of_nat n)" using \<open>c > 0\<close> by simp
next
  fix C n :: nat
  define d where "d \<equiv> nat \<lceil>1 / c\<rceil>"
  assume asm: "of_nat (d * C * n) \<le> f (of_nat n)"

  have "of_nat (C * n) = 1 * of_nat (C * n)" by simp
  also have "1 * of_nat (C * n) \<le> c * of_nat d * of_nat (C * n)"
  proof (rule mult_right_mono)
    from \<open>c > 0\<close> have "1 \<le> c * (1/c)" by simp
    also from \<open>c > 0\<close> have "... \<le> c * of_nat d"
      unfolding d_def by (intro mult_left_mono) (simp_all add: of_nat_ceiling)
    finally show  "c * of_nat d \<ge> 1" .
  qed simp
  also have "c * of_nat d * of_nat (C * n) = c * of_nat (d * C * n)" unfolding of_nat_mult mult.assoc ..
  also from asm and \<open>c > 0\<close> have "... \<le> c * f (of_nat n)" by (subst mult_le_cancel_iff2)
  finally show "of_nat (C * n) \<le> c * f (of_nat n)" .
qed


lemma superlinear_ae_mono:
  fixes f g
  assumes "superlinear f"
    and "\<forall>\<^sub>\<infinity>x. f (of_nat x) \<le> g (of_nat x)"
  shows "superlinear g"
proof -
  from \<open>superlinear f\<close> show "superlinear g" unfolding superlinear_def
  proof (intro allI, elim allE, ae_nat_elim add: \<open>\<forall>\<^sub>\<infinity>x. f (of_nat x) \<le> g (of_nat x)\<close>)
    fix C n :: nat
    assume "of_nat (C * n) \<le> f (of_nat n)"
    also assume "f (of_nat n) \<le> g (of_nat n)"
    finally show "of_nat (C * n) \<le> g (of_nat n)" .
  qed
qed


lemma superlinear_poly_powr:
  fixes c :: real
  assumes "c > 1"
  shows "superlinear (\<lambda>x. x powr c)"
  unfolding superlinear_def
proof (intro allI)
  fix C
  show "\<forall>\<^sub>\<infinity>n. of_nat (C * n) \<le> of_nat n powr c"
  proof (cases "C = 0")
    assume [simp]: "C \<noteq> 0"
    show ?thesis
    proof (rule Alm_all_natI')
      fix n :: nat
      assume asm: "n \<ge> max 2 (nat \<lceil>C powr (1 / (c-1))\<rceil>)"
      then have "n \<ge> 2" by (rule max.boundedE)

      have "ln C / (c - 1) = ln C * (1 / (c-1))" by simp
      also have "... = ln (C powr (1 / (c-1)))" by (simp add: ln_powr)
      also from asm have "... \<le> ln n" by force
      finally have "ln C / (c - 1) \<le> ln n" .
      with \<open>c > 1\<close> have "ln C \<le> ln n * (c - 1)" by (simp add: pos_divide_le_eq)
      then have *: "exp (ln C) \<le> exp (ln n * (c - 1))" ..

      from \<open>C \<noteq> 0\<close> have "C = exp (ln C)" by (subst exp_ln) force+
      also note *
      also have "exp (ln n * (c - 1)) = n powr (c - 1)" unfolding powr_def using \<open>n \<ge> 2\<close> by simp
      finally have "n * C \<le> n * n powr (c - 1)" using \<open>n \<ge> 2\<close> by simp
      also have "... = n powr c" using \<open>c > 1\<close> by (simp add: powr_mult_base)
      finally show "C * n \<le> n powr c" by (simp add: mult.commute)
    qed
  qed \<comment> \<open>case \<open>C = 0\<close> by\<close> simp
qed

lemma superlinear_poly_realpow:
  fixes c :: nat and f :: "real \<Rightarrow> real"
  defines "f n \<equiv> n ^ c"
  assumes "c > 1"
  shows "superlinear f"
proof -
  from \<open>c > 1\<close> have "superlinear (\<lambda>n. n powr c)" by (simp add: superlinear_poly_powr)
  then show "superlinear f" unfolding f_def
  proof (elim superlinear_ae_mono, intro Alm_all_natI')
    fix n :: nat
    assume "n \<ge> 1"
    then show "real n powr real c \<le> real n ^ c" by (simp add: powr_realpow)
  qed
qed

lemma superlinear_poly_nat:
  fixes c :: nat and f :: "nat \<Rightarrow> nat"
  defines "f n \<equiv> n ^ c"
  assumes "c > 1"
  shows "superlinear f"
proof -
  from \<open>c > 1\<close> have "superlinear (\<lambda>n::real. n ^ c)" by (fact superlinear_poly_realpow)
  then show "superlinear f" unfolding f_def superlinear_def of_nat_id
  proof (intro allI, elim allE, ae_nat_elim)
    fix C n
    assume "real (C * n) \<le> real n ^ c"
    also have "... = real (n ^ c)" by simp
    finally show "C * n \<le> n ^ c" unfolding of_nat_le_iff .
  qed
qed

end
