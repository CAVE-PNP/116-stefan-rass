theory Suppl_Discrete_Log
  imports "HOL-Library.Discrete" Suppl_Fun
begin


subsection\<open>Discrete Logarithm\<close>

\<comment> \<open>\<open>dlog\<close> defines \<open>\<lfloor>log\<^sub>2 n\<rfloor>\<close> over the natural numbers.\<close>
abbreviation dlog :: "nat \<Rightarrow> nat"
  where "dlog \<equiv> Discrete.log"

\<comment> \<open>\<open>clog\<close> defines \<open>\<lceil>log\<^sub>2 n\<rceil>\<close> over the natural numbers. Note that this is not correct over the reals.\<close>
abbreviation clog :: "nat \<Rightarrow> nat"
  where "clog n \<equiv> dlog (n-1) + 1"


lemma log_less: "n > 0 \<Longrightarrow> dlog n < n"
proof -
  assume "n > 0"
  have "dlog n < 2 ^ dlog n" by (rule less_exp)
  also have "... \<le> n" using \<open>n > 0\<close> by (rule log_exp2_le)
  finally show ?thesis .
qed

lemma log_le: "dlog n \<le> n"
  by (cases "n > 0") (simp_all add: less_imp_le log_less)

lemma dlog_altdef: "1 \<le> n \<Longrightarrow> dlog n = nat \<lfloor>log 2 n\<rfloor>"
  unfolding log_altdef by (subst if_not_P) fastforce+


lemma log_exp_m1: "dlog (2^k - 1) = k - 1"
proof (cases "k > 0")
  case True show ?thesis
  proof (intro log_eqI)
    \<comment> \<open>Isabelle automatically chooses the most general applicable interpretation of numerals,
      but the following results do not hold for all of those (and are not required to).\<close>
    let ?Z = "2::nat"

    from \<open>k > 0\<close> have "2^k \<ge> ?Z" using self_le_power[of 2 k] by fastforce
    then show "?Z^k - 1 > 0" by (simp add: \<open>k > 0\<close>)
    show "?Z^k - 1 < 2 * 2^(k - 1)" unfolding power_Suc[symmetric] by (simp add: \<open>k > 0\<close>)
    have "?Z^(k-1) < 2^k" by (simp add: \<open>k > 0\<close>)
    moreover have "a < b \<Longrightarrow> a \<le> b - 1" for a b :: nat by force
    ultimately show "?Z^(k - 1) \<le> 2^k - 1" by blast
  qed
qed (* case "k = 0" by *) simp


lemma dlog_times_exp:
  assumes "a > 0"
  shows "dlog (a * 2^k) = dlog a + k"
proof (induction k)
  case (Suc k)
  from \<open>a > 0\<close> have h1: "a * 2^k \<noteq> 0" by fastforce

  have "a * 2^Suc k = 2 * (a * 2^k)" by simp
  with arg_cong have "dlog (a * 2 ^ Suc k) = dlog (2 * (a * 2^k))" .
  also have "... = dlog (a * 2^k) + 1" using log_twice h1 unfolding Suc_eq_plus1 .
  also have "... = dlog a + Suc k" unfolding Suc.IH add.assoc Suc_eq_plus1 ..
  finally show ?case .
qed (* case "k = 0" by *) simp

lemma dlog_Suc:
  assumes "n > 0"
  shows "dlog (Suc n) = (if Suc n = 2 ^ dlog (Suc n) then Suc (dlog n) else dlog n)"
    (is "dlog ?Sn = ?rhs")
proof (cases "Suc n = 2 ^ dlog (Suc n)")
  case True
  then have n_eq: "n = 2 ^ dlog (Suc n) - 1" by simp

  from \<open>n > 0\<close> have "?Sn \<ge> 2" "n \<noteq> 0" by simp_all
  have "dlog ?Sn > 0" unfolding \<open>?Sn \<ge> 2\<close>[THEN log_rec] ..

  from if_P True have "?rhs = Suc (dlog n)" .
  also have "... = Suc (dlog (2 ^ dlog (Suc n) - 1))" by (subst n_eq) rule
  also have "... = Suc (dlog (Suc n) - 1)" unfolding log_exp_m1 ..
  also have "... = dlog (Suc n)" using Suc_diff_1 \<open>dlog ?Sn > 0\<close> .
  finally show "dlog ?Sn = ?rhs" ..
next
  case False
  with if_not_P have req: "?rhs = dlog n" .
  show "dlog (Suc n) = ?rhs" unfolding req
  proof (intro log_eqI)
    show "?Sn > 0" ..
    from log_exp2_le \<open>n > 0\<close> have "n \<ge> 2 ^ dlog n" .
    with le_SucI show "?Sn \<ge> 2 ^ dlog n" .

    have "?Sn > 2 ^ dlog ?Sn"
    proof (intro le_neq_trans)
      have "?Sn > 0" ..
      with log_exp2_le show "?Sn \<ge> 2 ^ dlog ?Sn" .
      from \<open>?Sn \<noteq> 2 ^ dlog ?Sn\<close> show "2 ^ dlog ?Sn \<noteq> ?Sn" ..
    qed
    then have "n \<ge> 2 ^ dlog ?Sn" by simp
    with log_le_iff have "dlog n \<ge> dlog (2 ^ (dlog ?Sn))" .
    then have "dlog n \<ge> dlog ?Sn" unfolding log_exp .

    moreover have "dlog n \<le> dlog ?Sn" using log_le_iff less_imp_le lessI .
    ultimately have deq: "dlog ?Sn = dlog n" by (rule le_antisym)
    from log_exp2_gt[of ?Sn] show "?Sn < 2 * 2 ^ dlog n" unfolding deq .
  qed
qed

corollary dlog_add1_le: "dlog (n + 1) \<le> dlog n + 1"
proof (cases "n > 0")
  assume "n > 0" thus ?thesis by (fold Suc_eq_plus1, subst dlog_Suc) simp_all
qed (* case "n = 0" by *) simp


subsubsection\<open>Discrete Ceiling Log\<close>

lemma clog_exp: "0 < n \<Longrightarrow> clog (2^n) = n" unfolding log_exp_m1 by fastforce

lemma clog_le: "0 < n \<Longrightarrow> clog n \<le> n"
proof -
  assume "n > 0"
  have "dlog (n-1) \<le> n-1" by (rule log_le)
  then have "clog n \<le> n-1 + 1" by (unfold add_le_cancel_right)
  also have "... = n" using \<open>n > 0\<close> by simp
  finally show "clog n \<le> n" .
qed

lemma power_two_decompose:
  fixes n::nat
  assumes "1 \<le> n"
  obtains k m::nat
  where "n = 2^k + m" and "m < 2^k"
proof -
  have "strict_mono (\<lambda>k. (2::nat)^k)" by (intro strict_monoI) simp
  then obtain k where "2^k \<le> n" and *: "\<forall>k'. 2^k' \<le> n \<longrightarrow> k' \<le> k"
    using assms nat_strict_mono_greatest[of "\<lambda>k. 2^k" n] by auto

  define m where "m \<equiv> n - 2^k"

  have "n = 2^k + m" using m_def \<open>2^k \<le> n\<close> by simp

  moreover have "m < 2^k" proof (rule ccontr)
    assume "\<not> m < 2^k"
    hence "2^(k+1) \<le> n" using m_def by simp
    thus False using * by fastforce
  qed

  ultimately show thesis using that by simp
qed

lemma log_eq1:
  fixes k m::nat
  assumes "0 \<le> m" "m < 2^k"
  shows "dlog (2^k + m) = k"
  using assms log_eqI by force

lemma log_eq2:
  fixes k m::nat
  assumes "1 \<le> m" "m < 2^k"
  shows "nat \<lceil>log 2 (2^k + m)\<rceil> = k + 1"
proof -
  let ?n = "2^k+m"
  have "k < log 2 ?n"
    using assms less_log2_of_power[of k ?n] by simp
  moreover have "log 2 ?n \<le> k+1"
    using assms log2_of_power_le[of ?n "k+1"] by simp
  ultimately show ?thesis by linarith
qed

lemma log_altdef_ceil:
  assumes "2 \<le> (n::nat)"
  shows "clog n = nat \<lceil>log 2 n\<rceil>"
proof -
  from assms have "1 \<le> n" by simp
  with power_two_decompose obtain k m where km_def: "n = 2^k + m" "m < 2^k" .

  show "dlog (n-1) + 1 = nat \<lceil>log 2 n\<rceil>" proof (cases "m = 0")
    case True
    then have k_def: "n = 2^k" using \<open>n = 2^k + m\<close> by simp

    have "dlog (n-1) + 1 = (k-1) + 1" unfolding add_right_cancel k_def by (rule log_exp_m1)
    also have "... = k"
    proof (intro le_add_diff_inverse2)
      have "(2::nat) ^ 1 \<le> 2 ^ k" using assms unfolding k_def by simp
      then show "1 \<le> k" by (intro power_le_imp_le_exp) simp_all
    qed
    also have "... = dlog (2^k)" using log_exp ..
    also have "... = nat \<lceil>log 2 ((2::nat)^k)\<rceil>" by (subst dlog_altdef) simp_all
    also have "... = nat \<lceil>log 2 n\<rceil>" unfolding k_def ..
    finally show ?thesis .
  next
    case False
    then have \<open>1 \<le> m\<close> \<open>0 \<le> m-1\<close> by simp_all
    from \<open>m < 2^k\<close> have "m-1 < 2^k" by (rule less_imp_diff_less)

    have "dlog (n-1) = dlog (2^k + (m-1))" unfolding km_def
      using \<open>1 \<le> m\<close> by (subst diff_add_assoc) simp_all
    also have "... = k" using \<open>0 \<le> m-1\<close> \<open>m-1 < 2^k\<close> by (rule log_eq1)
    finally have "dlog (n-1) + 1 = k + 1" unfolding add_right_cancel .
    also have "... = nat \<lceil>log 2 n\<rceil>" unfolding km_def
      using \<open>1 \<le> m\<close> \<open>m < 2^k\<close> by (subst log_eq2) simp_all
    finally show ?thesis .
  qed
qed


end
