theory Threshold_Functions
  imports Main "HOL.Binomial" "HOL.Limits" "Supplementary/Misc"
begin

definition mono
  where "mono Q \<equiv> \<forall>A B. A \<subseteq> B \<longrightarrow> Q A \<longrightarrow> Q B"

definition nontriv
  where "nontriv Q \<equiv> \<exists>A B. finite A \<and> Q A \<and> finite B \<and> ~ Q B"

lemma mono_nontriv_empty: "mono Q \<Longrightarrow> nontriv Q \<Longrightarrow> ~ Q {}"
  unfolding mono_def nontriv_def by blast

(* probability of a random k-subset of {1..n} having Q *)
definition P_k
  where "P_k n k Q \<equiv> card {A\<in>Pow {0..<n}. card A = k \<and> Q A} / (binomial n k)"

lemma
  assumes "mono Q" and "nontriv Q"
  shows mono_non_triv_0: "\<forall>n. P_k n 0 Q = 0"
    and mono_non_triv_n: "\<exists>N. \<forall>n\<ge>N. P_k n n Q = 1"
proof -
  show "\<forall>n. P_k n 0 Q = 0" proof safe
    fix n::nat
    have "{A\<in>Pow {1..n}. card A = 0} = {{}}"
      using finite_subset by fastforce
    moreover have "~ Q {}"
      using assms by (rule mono_nontriv_empty)
    ultimately have "{A\<in>Pow {0..<n}. card A = 0 \<and> Q A} = {}"
      by (simp add: card_eq_0_iff finite_subset)
    thus "P_k n 0 Q = 0" unfolding P_k_def by simp
  qed

  show "\<exists>N. \<forall>n\<ge>N. P_k n n Q = 1" proof -
    from \<open>nontriv Q\<close> obtain A::"nat set" where "Q A" "finite A"
      unfolding nontriv_def by blast
    then obtain N::nat where "A \<subseteq> {0..<N}"
      using finite_subset_interval by blast
    with \<open>Q A\<close> have "Q {0..<N}"
      using \<open>mono Q\<close> unfolding mono_def by blast

    {
      fix n assume "n\<ge>N"
      then have "{0..<N} \<subseteq> {0..<n}"
        unfolding ivl_subset by blast
      with \<open>Q {0..<N}\<close> \<open>mono Q\<close> have "Q {0..<n}"
        unfolding mono_def by blast
      moreover have "{A\<in>Pow {0..<n}. card A = n} = {{0..<n}}"
        using Pow_card_singleton[of "{0..<n}"] by simp
      ultimately have "{A\<in>Pow {0..<n}. card A = n \<and> Q A} = {{0..<n}}" by blast
      hence "P_k n n Q = 1" unfolding P_k_def binomial_n_n by simp
    }

    thus ?thesis by blast
  qed
qed

definition almost_every
  where "almost_every k Q \<equiv> (\<lambda>n. P_k n (k n) Q) \<longlonglongrightarrow> 1"

definition almost_none 
  where "almost_none k Q \<equiv> (\<lambda>n. P_k n (k n) Q) \<longlonglongrightarrow> 0"

definition threshold
  where "threshold M Q \<equiv>
    \<forall>m. let q=\<lambda>n. (m n)/of_nat (M n) in
      (q \<longlonglongrightarrow> 0) \<longrightarrow> almost_none m Q
    \<and> (q \<longlonglongrightarrow> 1) \<longrightarrow> almost_every m Q"

(*every non-trivial monotone increasing property has a threshold function *)
theorem mono_ex_th:
  fixes Q :: "nat set \<Rightarrow> bool"
  assumes "mono Q"
      and "nontriv Q"
    obtains M where "threshold M Q"
sorry

end