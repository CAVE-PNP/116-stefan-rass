theory Threshold_Functions
  imports Main "HOL.Binomial" "HOL.Limits" "Supplementary/Misc"
begin

lemma mono_altdef:
  fixes Q::"'a set \<Rightarrow> bool"
  shows "mono Q = (\<forall>A B. A \<subseteq> B \<longrightarrow> Q A \<longrightarrow> Q B)"
unfolding mono_def le_bool_def ..

definition nontriv
  where "nontriv Q \<equiv> \<exists>A B. finite A \<and> Q A \<and> finite B \<and> ~ Q B"

lemma mono_nontriv_empty: "mono Q \<Longrightarrow> nontriv Q \<Longrightarrow> ~ Q {}"
  unfolding mono_altdef nontriv_def by blast

(* probability of a random k-subset of {1..n} having Q *)
definition P_k
  where "P_k n k Q \<equiv> card {A\<in>Pow {0..<n}. card A = k \<and> Q A} / (n choose k)"

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
      using assms(1-2) by (rule mono_nontriv_empty)
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
      using \<open>mono Q\<close> unfolding mono_altdef by blast

    {
      fix n assume "n\<ge>N"
      then have "{0..<N} \<subseteq> {0..<n}"
        unfolding ivl_subset by blast
      with \<open>Q {0..<N}\<close> \<open>mono Q\<close> have "Q {0..<n}"
        unfolding mono_altdef by blast
      moreover have "{A\<in>Pow {0..<n}. card A = n} = {{0..<n}}"
        using Pow_card_singleton[of "{0..<n}"] by simp
      ultimately have "{A\<in>Pow {0..<n}. card A = n \<and> Q A} = {{0..<n}}" by blast
      hence "P_k n n Q = 1" unfolding P_k_def binomial_n_n by simp
    }

    thus ?thesis by blast
  qed
qed

lemma P_k_mono:
  fixes n::nat
  assumes "1\<le>n" "mono Q" "Suc k \<le> n"
  shows "P_k n k Q \<le> P_k n (Suc k) Q"
proof - (* Beweisidee: Josef Greilhuber *)
  let ?P = "\<lambda>k. {A\<in>Pow {0..<n}. card A = k}"
  let ?M = "\<lambda>k. {A\<in>Pow {0..<n}. card A = k \<and> Q A}"
  let ?c = "\<lambda>A. {0..<n} - A"
  have 1: "\<And>k A. A \<in> ?P k \<Longrightarrow> card (?c A) = n-k" proof -
    fix k A assume "A \<in> ?P k"
    then have "finite A" "finite (?c A)" "A \<inter> ?c A = {}" "A \<union> ?c A = {0..<n}" "card A = k"
      using finite_subset by blast+
    thus "card (?c A) = n-k"
      using card_Un_disjoint[of A "?c A"] by simp
  qed

  have "\<And>A x. Q A \<longrightarrow> Q (A \<union> {x})" using \<open>mono Q\<close>
    unfolding mono_altdef by blast
  then have 2: "\<And>A x. of_bool (Q A) \<le> (of_bool (Q (A \<union> {x})) :: nat)"
    using of_bool_mono by blast
  have finP: "\<And>k. finite (?P k)" by simp

  define L where "L \<equiv> {(A, x). A\<in>?P k       \<and> x \<in> ?c A}"
  define R where "R \<equiv> {(B, x). B\<in>?P (Suc k) \<and> x \<in> B   }"
  have L_altdef: "L = Sigma (?P k) ?c" unfolding L_def by fastforce
  have R_altdef: "R = Sigma (?P (Suc k)) id" unfolding R_def by fastforce

  define g::"nat set \<times> nat \<Rightarrow> nat set \<times> nat" where "g \<equiv> \<lambda>(A,x). (A \<union> {x}, x)"
  have "bij_betw g L R" sorry
  from sum.reindex_bij_betw[OF this] g_def
  have 3: "\<And>h. ( \<Sum>(A,x)\<in>L. h ((A \<union> {x}, x)) ) = (\<Sum>Bx\<in>R. h Bx)"
    by (metis (mono_tags, lifting) prod.case_distrib split_cong sum.cong)
  
  find_theorems  "sum"  "Sigma" (* relevant! *)
  from count_with_prop[of "?P k" Q] finP[of k]
  have "card (?M k) = (\<Sum>A\<in>(?P k). of_bool (Q A))" by fastforce
  then have "(n-k) * card (?M k) = (\<Sum>A\<in>(?P k). \<Sum>x\<in>(?c A). of_bool (Q A))"
    using 1[where k=k] sorry

  also have "\<dots> = (\<Sum>(A, x)\<in>L. of_bool (Q A))"
    unfolding L_altdef using sum.Sigma[of "?P k" ?c] finP[of k] by fast
  also from 2 sum_mono have "\<dots> \<le> (\<Sum>(A, x)\<in>L. of_bool (Q (A \<union> {x})))"
    by (metis (mono_tags, lifting) case_prod_conv dual_order.eq_iff split_cong)
  also have "\<dots> = sum (\<lambda>(B,x). of_bool (Q B)) R"
    using 3[of "\<lambda>(B,x). of_bool (Q B)"] by fast
  also have "\<dots> = (\<Sum>B\<in>(?P (Suc k)). \<Sum>x\<in>B. of_bool (Q B))"
    unfolding R_altdef using sum.Sigma[of "?P (Suc k)" id "\<lambda>B x. of_bool (Q B)"] finP[of "Suc k"]
    by (smt (verit, ccfv_SIG) card_eq_0_iff id_apply mem_Collect_eq nat.simps(3) sum.cong)

  also have "\<dots> = (Suc k) * (\<Sum>B\<in>(?P (Suc k)).  of_bool (Q B))" sorry
  also from count_with_prop have "\<dots> = (Suc k) * card (?M (Suc k))" sorry
  ultimately have "(n-k) * card (?M k) \<le> (Suc k) * card (?M (Suc k))" by argo
  thus ?thesis unfolding P_k_def using binomial_fact_lemma assms(1,3) sorry
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