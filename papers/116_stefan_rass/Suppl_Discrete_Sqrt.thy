theory Suppl_Discrete_Sqrt
  imports "HOL-Library.Discrete" Suppl_Discrete_Log Suppl_Fun
begin


subsection\<open>Discrete Square Root\<close>

abbreviation (input) is_square :: "nat \<Rightarrow> bool" where
  "is_square n \<equiv> (\<exists>m. n = m\<^sup>2)"

\<comment> \<open>\<open>dsqrt\<close> defines \<open>\<lfloor>\<surd>n\<rfloor>\<close> over the natural numbers.\<close>
abbreviation dsqrt :: "nat \<Rightarrow> nat"
  where "dsqrt \<equiv> Discrete.sqrt"


lemma sqrt_altdef_nat: "dsqrt n = nat \<lfloor>sqrt n\<rfloor>"
proof -
  have *: "(sqrt n)\<^sup>2 = n" by simp

  have "(dsqrt n)\<^sup>2 \<le> n" by simp
  then have "(dsqrt n)\<^sup>2 \<le> (sqrt n)\<^sup>2" unfolding * by simp
  then have upper: "dsqrt n \<le> sqrt n" by (simp add: real_le_rsqrt)

  have "n < (dsqrt n + 1)\<^sup>2" using Suc_sqrt_power2_gt by simp
  then have "(sqrt n)\<^sup>2 < real ( (dsqrt n + 1)\<^sup>2 )" unfolding * by (rule less_imp_of_nat_less)
  then have "(sqrt n)\<^sup>2 < ( real (dsqrt n + 1) )\<^sup>2" by simp
  then have lower: "sqrt n < dsqrt n + 1" using power2_less_imp_less[of "sqrt n"] by force

  from upper and lower show "dsqrt n = nat \<lfloor>sqrt n\<rfloor>" by (intro floor_eq4[symmetric]) auto
qed

corollary sqrt_altdef: "dsqrt n = \<lfloor>sqrt n\<rfloor>" using sqrt_altdef_nat int_eq_iff by force

lemma sqrt_ceil_floor:
  fixes n :: nat
  assumes "n > 0"
  shows "\<lceil>sqrt n\<rceil> = \<lfloor>sqrt (n - 1)\<rfloor> + 1"
proof -
  have h0: "Suc (n - 1) = n" using \<open>n > 0\<close> by simp
  have h1: "dsqrt n = (if is_square n then dsqrt (n - 1) + 1 else dsqrt (n - 1))"
    using sqrt_Suc[of "n - 1"] unfolding h0 unfolding Suc_eq_plus1 .

  have "\<lfloor>sqrt (n - 1)\<rfloor> + 1 - 1 = \<lfloor>sqrt (n - 1)\<rfloor>" by simp
  also have "... \<le> sqrt (n - 1)" by simp
  also have "... < sqrt n" using \<open>n > 0\<close> by simp
  finally have "of_int (\<lfloor>sqrt (n - 1)\<rfloor> + 1) - 1 < sqrt n" by simp
  then have upper: "\<lfloor>sqrt (n - 1)\<rfloor> + 1 \<le> \<lceil>sqrt n\<rceil>" by (subst le_ceiling_iff)

  have "sqrt n \<le> dsqrt (n - 1) + 1"
  proof (cases "is_square n")
    case True
    then have "dsqrt (n - 1) + 1 = dsqrt n" using h1 by presburger
    also have "... = sqrt n" using \<open>is_square n\<close> by auto
    finally show "sqrt n \<le> dsqrt (n - 1) + 1" by argo
  next
    case False
    then have "dsqrt (n - 1) + 1 = dsqrt n + 1" using h1 by presburger
    also have "... = \<lfloor>sqrt n\<rfloor> + 1" by (simp add: sqrt_altdef)
    also have "... > sqrt n" by simp
    finally show "sqrt n \<le> dsqrt (n - 1) + 1" by simp
  qed
  moreover have "dsqrt (n - 1) + 1 = \<lfloor>sqrt (n - 1)\<rfloor> + 1" using sqrt_altdef by simp
  ultimately have "sqrt n \<le> \<lfloor>sqrt (n - 1)\<rfloor> + 1" by auto
  then have lower: "\<lceil>sqrt n\<rceil> \<le> \<lfloor>sqrt (n - 1)\<rfloor> + 1" by (subst ceiling_le_iff)

  from lower and upper show ?thesis by (rule antisym)
qed


subsubsection\<open>Integer Squares\<close>

\<comment> \<open>\<open>prev_square\<close> defines \<open>\<lfloor>\<surd>n\<rfloor>\<^sup>2\<close> or \<^term>\<open>\<lambda>n. Max {sq::nat. is_square sq \<and> sq \<le> n}\<close>.\<close>
abbreviation prev_square :: "nat \<Rightarrow> nat"
  where "prev_square n \<equiv> (dsqrt n)\<^sup>2"

\<comment> \<open>\<open>next_square\<close> defines \<open>\<lceil>\<surd>n\<rceil>\<^sup>2\<close> or \<^term>\<open>\<lambda>n. Min {sq::nat. is_square sq \<and> sq > n}\<close>.\<close>
definition next_square :: "nat \<Rightarrow> nat" where
  next_sq_def[simp]: "next_square n = (dsqrt (n - 1) + 1)\<^sup>2"

\<comment> \<open>The pattern \<open>\<lceil>f n\<rceil> = \<lfloor>f (n-1)\<rfloor> + 1\<close> seems to hold for arbitrary functions
  that exhibit sub-linear asymptotic growth.\<close>


corollary prev_sq_correct: "is_square (prev_square n)" by blast

\<comment> \<open>\<^term>\<open>prev_square n \<le> n\<close> is proven in @{thm Discrete.sqrt_power2_le}\<close>

corollary next_sq_correct1: "is_square (next_square n)" by simp

lemma next_sq_gt0: "next_square n > 0" by simp

lemma next_sq_eq: "n > 0 \<Longrightarrow> is_square n \<Longrightarrow> next_square n = n"
proof -
  assume "n > 0" and "is_square n"
  with sqrt_Suc[of "n - 1"] have *: "dsqrt n = dsqrt (n - 1) + 1" by simp

  from \<open>is_square n\<close> have "n = (dsqrt n)\<^sup>2" by fastforce
  then have "n = (dsqrt (n - 1) + 1)\<^sup>2" by (unfold *)
  then show ?thesis by simp
qed

lemma next_sq_gt: "\<not> is_square n \<Longrightarrow> n < next_square n"
proof (cases "n > 0")
  assume "n > 0" and "\<not> is_square n"
  with sqrt_Suc[of "n - 1"] have *: "dsqrt n = dsqrt (n - 1)" by force

  from Suc_sqrt_power2_gt have "n < (dsqrt n + 1)\<^sup>2" by simp
  then have "n < (dsqrt (n - 1) + 1)\<^sup>2" by (unfold *)
  then show ?thesis by simp
qed (* case "n = 0" by *) simp

lemma next_sq_correct2: "n \<le> next_square n"
proof (cases "n > 0")
  case True show ?thesis
  proof (cases "is_square n")
    case True
    with next_sq_eq[of n] and \<open>n > 0\<close> show ?thesis by (intro eq_imp_le) (rule sym)
  next
    case False
    with next_sq_gt[of n] and \<open>n > 0\<close> show ?thesis by (intro less_imp_le_nat)
  qed
qed (* case "n = 0" by *) simp

corollary prev_sq_le_next_sq: "prev_square n \<le> next_square n"
  using le_trans and sqrt_power2_le and next_sq_correct2 .

corollary prev_next_sq_eq: "prev_square n = next_square n \<longleftrightarrow> n = next_square n"
proof (intro iffI)
  assume sqs: "prev_square n = next_square n"
  show "n = next_square n" using sqrt_power2_le[of n] next_sq_correct2[of n]
    unfolding sqs by (intro le_antisym)
next
  assume nsq: "n = next_square n"
  obtain m where m: "n = m\<^sup>2" using next_sq_correct1[of n] by (fold nsq) (elim exE)
  have "prev_square n = n" unfolding \<open>n = m\<^sup>2\<close> by simp
  also note \<open>n = next_square n\<close>
  finally show "prev_square n = next_square n" .
qed

lemma next_sq_le_greater_sq: "next_square n \<le> (dsqrt n + 1)\<^sup>2"
  unfolding next_sq_def using mono_sqrt' and power_mono by simp

lemma adj_sq_real: "(x + 1)\<^sup>2 - x\<^sup>2 = 2 * x + 1" for x :: real by algebra
lemma adj_sq_nat: "(x + 1)\<^sup>2 - x\<^sup>2 = 2 * x + 1" for x :: nat
  unfolding power2_eq_square mult_2 by simp

lemma next_prev_sq_diff: "next_square n - prev_square n \<le> 2 * (dsqrt n) + 1"
proof -
  let ?r = "dsqrt n"
  have "next_square n - prev_square n \<le> (dsqrt n + 1)\<^sup>2 - (dsqrt n)\<^sup>2"
    using next_sq_le_greater_sq by (rule diff_le_mono)
  also have "... = 2 * dsqrt n + 1" by (rule adj_sq_nat)
  finally show ?thesis .
qed

corollary next_sq_diff: "next_square n - n \<le> 2 * (dsqrt n) + 1"
proof -
  have "next_square n - n \<le> next_square n - prev_square n" using sqrt_power2_le by (rule diff_le_mono2)
  also have "... \<le> 2 * (dsqrt n) + 1" by (rule next_prev_sq_diff)
  finally show ?thesis .
qed

lemma next_sq_correct3: "n > 0 \<Longrightarrow> next_square n = \<lceil>sqrt n\<rceil>\<^sup>2"
  using sqrt_ceil_floor sqrt_altdef by simp


end
