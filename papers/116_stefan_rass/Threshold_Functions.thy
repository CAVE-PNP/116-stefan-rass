theory Threshold_Functions
  imports Main "HOL.Binomial" "HOL.Limits" "Supplementary/Misc"
begin

definition mono
  where "mono Q \<equiv> \<forall>A B. A \<subseteq> B \<longrightarrow> Q A \<longrightarrow> Q B"

definition nontriv
  where "nontriv Q \<equiv> \<exists>A B. Q A \<and> ~ Q B"

lemma mono_nontriv_empty: "mono Q \<Longrightarrow> nontriv Q \<Longrightarrow> ~ Q {}"
  unfolding mono_def nontriv_def by blast

(* probability of a random k-subset of {1..n} having Q *)
definition P_k
  where "P_k n k Q \<equiv> card {A\<in>Pow {0..<n}. card A = k \<and> Q A} / (binomial n k)"

lemma
  assumes "mono Q" and "nontriv Q"
  shows mono_non_triv_0: "P_k n 0 Q = 0"
    and mono_non_triv_n: "P_k n n Q = 1"
  using assms proof -
  fix Q::"nat set \<Rightarrow> bool"
  assume mono: "mono Q" and nontriv: "nontriv Q"

  show "P_k n 0 Q = 0" proof -
    have "{A\<in>Pow {1..n}. card A = 0} = {{}}"
      using finite_subset by fastforce
    moreover have "~ Q {}"
      using mono nontriv by (rule mono_nontriv_empty)
    ultimately have "{A\<in>Pow {0..<n}. card A = 0 \<and> Q A} = {}"
      by (simp add: card_eq_0_iff finite_subset)
    thus ?thesis unfolding P_k_def by simp
  qed

  show "P_k n n Q = 1" proof -
    have "Q {0..<n}" sorry (* Not true! - only eventually *)
    moreover have "{A\<in>Pow {0..<n}. card A = n} = {{0..<n}}"
      using Pow_card_singleton[of "{0..<n}"] by simp
    ultimately have "{A\<in>Pow {0..<n}. card A = n \<and> Q A} = {{0..<n}}" by blast
    thus ?thesis unfolding P_k_def binomial_n_n by simp
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