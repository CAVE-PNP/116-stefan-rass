subsection\<open>Limits\<close>

theory Limit
  imports Complex_Main
begin


text\<open>Helpful lemmas centered around \<^const>\<open>LIMSEQ\<close> (\<^term>\<open>x\<^sub>i \<longlonglongrightarrow> x\<close>).\<close>

lemma dominates_altdef:
  fixes c :: real
  assumes "\<And>n. T n \<noteq> 0"
    and T_dominates_t: "(\<lambda>n. t n / T n) \<longlonglongrightarrow> 0"
  shows "\<exists>N. \<forall>n\<ge>N. \<bar>c * t n\<bar> < \<bar>T n\<bar>"
proof (cases "c = 0")
  assume "c = 0"
  show ?thesis proof (intro exI allI impI)
    fix n
    have "\<bar>c * t n\<bar> = 0" unfolding \<open>c = 0\<close> by simp
    also have "0 < \<bar>T n\<bar>" using \<open>T n \<noteq> 0\<close> by simp
    finally show "\<bar>c * t n\<bar> < \<bar>T n\<bar>" .
  qed
next
  let ?f = "\<lambda>n. t n / T n"
  assume "c \<noteq> 0"
  define c' where c': "c' \<equiv> 1 / c"
  from \<open>c \<noteq> 0\<close> have "c' \<noteq> 0" unfolding c' by simp

  with T_dominates_t have "\<exists>N. \<forall>n\<ge>N. \<bar>?f n\<bar> < \<bar>c'\<bar>"
    unfolding LIMSEQ_def dist_real_def diff_0_right by force
  then obtain N where "\<bar>?f n\<bar> < \<bar>c'\<bar>" if "n \<ge> N" for n by blast

  have "\<bar>c * t n\<bar> < \<bar>T n\<bar>" if "n \<ge> N" for n
  proof -
    from \<open>T n \<noteq> 0\<close> have "\<bar>T n\<bar> > 0" unfolding zero_less_abs_iff .
    from \<open>c \<noteq> 0\<close> have "\<bar>c\<bar> > 0" unfolding zero_less_abs_iff .

    have "\<bar>?f n\<bar> < \<bar>c'\<bar>" using \<open>n \<ge> N\<close> by fact
    then have "\<bar>t n\<bar> / \<bar>T n\<bar> < 1 / \<bar>c\<bar>" unfolding c' abs_divide abs_one .
    then have "\<bar>t n\<bar> < \<bar>T n\<bar> / \<bar>c\<bar>" unfolding \<open>\<bar>T n\<bar> > 0\<close>[THEN pos_divide_less_eq] by argo
    then show "\<bar>c * t n\<bar> < \<bar>T n\<bar>" unfolding \<open>\<bar>c\<bar> > 0\<close>[THEN pos_less_divide_eq] abs_mult by argo
  qed
  then show "\<exists>N. \<forall>n\<ge>N. \<bar>c * t n\<bar> < \<bar>T n\<bar>" by blast
qed

end
