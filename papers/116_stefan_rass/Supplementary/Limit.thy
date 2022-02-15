subsection\<open>Limits\<close>

theory Limit
  imports Complex_Main
begin


text\<open>Helpful lemmas centered around \<^const>\<open>LIMSEQ\<close> (\<^term>\<open>x\<^sub>i \<longlonglongrightarrow> x\<close>).\<close>

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
  
  \<comment> \<open>The following can be considered boilerplate necessary due to the nested quantification.\<close>
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

end
