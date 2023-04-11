section\<open>Discrete Functions\<close>

subsection\<open>Discrete Logarithm\<close>

theory Discrete_Log
  imports "./Misc" "HOL-Library.Discrete"
begin


lemma Suc_div_le: "d > 1 \<Longrightarrow> n \<ge> d \<Longrightarrow> Suc (n div d) \<le> n" by (simp add: Suc_leI)

theorem full_nat_induct'[case_names step]:
  assumes step: "\<And>n. (\<And>m. Suc m \<le> n \<Longrightarrow> P m) \<Longrightarrow> P n"
  shows "P n"
  using step full_nat_induct by blast

lemma log_induct[consumes 1, case_names less div]:
  fixes b n :: nat
  assumes "b > 1"
  assumes less: "\<And>n. n < b \<Longrightarrow> P n"
  assumes div: "\<And>n. n \<ge> b \<Longrightarrow> P (n div b) \<Longrightarrow> P n"
  shows "P n"
proof (induction n rule: full_nat_induct')
  case (step n)
  then show ?case
  proof (cases "n \<ge> b", unfold not_le)
    assume "n < b"
    with less show "P n" .
  next
    assume "n \<ge> b"
    moreover with \<open>b > 1\<close> have "P (n div b)" by (intro step.IH) (fact Suc_div_le)
    ultimately show "P n" by (fact div)
  qed
qed


text\<open>Based on \<^theory>\<open>HOL-Library.Discrete\<close>, generalizes \<^const>\<open>Discrete.log\<close>.\<close>

fun nat_log :: "nat \<Rightarrow> nat \<Rightarrow> nat" \<comment> \<open>\<open>\<lfloor>log\<^sub>b n\<rfloor>\<close> over the natural numbers\<close>
  where nat_log_def[simp del]: "nat_log b i = (if b > 1 \<and> i \<ge> b then Suc (nat_log b (i div b)) else 0)"


lemma nat_log_0[simp]:
  shows "\<not> b > 1 \<Longrightarrow> nat_log b i = 0"
    and "\<not> i \<ge> b \<Longrightarrow> nat_log b i = 0"
    and "\<not> (b > 1 \<and> i \<ge> b) \<Longrightarrow> nat_log b i = 0" by (auto simp: nat_log_def)

locale nat_log_base =
  fixes b :: nat
  assumes valid_base: "b > 1"
  notes induct = log_induct[OF valid_base, case_names less div]
begin

lemma rec[simp]: "nat_log b n = Suc (nat_log b (n div b))" if "n \<ge> b"
  using valid_base and that by (subst nat_log_def) presburger

lemmas rec' = rec[symmetric]

end

declare nat_log_base.intro[intro!, simp]
global_interpretation log2: nat_log_base 2 by simp


lemma log2_induct'[case_names zero one div]:
  fixes n :: nat
  assumes "P 0" and "P 1"
  assumes step: "\<And>n. n \<ge> 2 \<Longrightarrow> P (n div 2) \<Longrightarrow> P n"
  shows "P n"
proof (induction n rule: log2.induct)
  case (less n)
  then have "n = 0 \<or> n = 1" by linarith
  with \<open>P 0\<close> and \<open>P 1\<close> show ?case by blast
next
  case (div n)
  with step show ?case .
qed

lemma log2_induct[consumes 1, case_names one div]:
  fixes n :: nat
  assumes "n > 0" and "P 1"
  assumes step: "\<And>n. n \<ge> 2 \<Longrightarrow> P (n div 2) \<Longrightarrow> P n"
  shows "P n"
  using \<open>n > 0\<close>
proof (induction rule: log2_induct')
  case (div n)
  from \<open>n \<ge> 2\<close> have "n div 2 > 0" by force
  with step div.hyps div.IH show ?case .
qed (use \<open>n > 0\<close> \<open>P 1\<close> in blast)+


lemma nat_log_zero_rev: "nat_log b i = 0 \<longleftrightarrow> b \<le> 1 \<or> i < b" by (force iff: not_le simp: nat_log.simps)
lemma nat_log_zero_rev': "nat_log b i \<noteq> 0 \<longleftrightarrow> b > 1 \<and> i \<ge> b"
  unfolding nat_log_zero_rev de_Morgan_disj not_less not_le ..

lemma nat_log_Suc_ge: "nat_log b i \<le> nat_log b (Suc i)"
proof (cases "b > 1")
  assume "b > 1" thus ?thesis
  proof (induction i rule: log_induct)
    case (div n)
    from \<open>n \<ge> b\<close> have "Suc n \<ge> b" by (fact le_SucI)

    from \<open>b > 1\<close> and \<open>n \<ge> b\<close> have "nat_log b n = Suc (nat_log b (n div b))" by (subst nat_log.simps) argo
    also have "... \<le> Suc (nat_log b (Suc n div b))" unfolding Suc_le_mono
    proof -
      from div.IH show "nat_log b (n div b) \<le> nat_log b (Suc n div b)"
        unfolding div_Suc by (rule ifI) blast
    qed
    also from \<open>b > 1\<close> and \<open>Suc n \<ge> b\<close> have "... = nat_log b (Suc n)" by (subst (2) nat_log.simps) argo
    finally show ?case .
  qed simp
qed \<comment> \<open>case \<open>b \<le> 1\<close> by\<close> force

lemma nat_log_mono: "mono (nat_log b)"
  unfolding incseq_Suc_iff using nat_log_Suc_ge ..

lemmas nat_log_le_iff[intro?] = monoD[OF nat_log_mono]


context nat_log_base
begin

lemma mult_b: "nat_log b (b * n) = Suc (nat_log b n)" if "n > 0" using valid_base and that
proof (induction n rule: log_induct)
  case (div n)
  from \<open>b > 1\<close> and \<open>n \<ge> b\<close> show ?case by (subst nat_log_def) auto
qed \<comment> \<open>case \<open>n < b\<close> by\<close> (simp add: nat_log_def)

lemma (in -) nat_log_div[simp]: "nat_log b (n div b) = nat_log b n - 1"
proof (cases "b > 1 \<and> n \<ge> b")
  assume "b > 1 \<and> n \<ge> b"
  then have "nat_log b n - 1 = nat_log b (n div b) + 1 - 1" by (subst nat_log_def) presburger
  also have "... = nat_log b (n div b)" by force
  finally show ?thesis ..
next
  assume "\<not> (b > 1 \<and> n \<ge> b)"
  then have h1: "nat_log b n = 0" by simp
  then have h2: "nat_log b (n div b) = 0" unfolding nat_log_zero_rev by force
  show "nat_log b (n div b) = nat_log b n - 1" unfolding h1 h2 by simp
qed


lemma exp_le: "b ^ nat_log b n \<le> n" if "n > 0" using valid_base and that
proof (induction n rule: log_induct)
  case (div n)
  from \<open>b > 1\<close> and \<open>n \<ge> b\<close> have h1: "n div b > 0" and h2: "nat_log b n > 0"
    by (auto simp: div_greater_zero_iff nat_log_def)

  have "b ^ nat_log b n = b * b ^ (nat_log b (n div b))"
    unfolding power_Suc[symmetric] nat_log_div Suc_diff_1[OF h2] ..
  also have "... \<le> b * (n div b)" using h1 by (intro mult_le_mono2 div.IH)
  also have "... \<le> n" by (fact times_div_less_eq_dividend)
  finally show ?case .
qed \<comment> \<open>case \<open>n < b\<close> by\<close> fastforce


lemma (in -) div_lt_rev_mono:
  fixes a b d :: nat
  shows "a div d < b div d \<Longrightarrow> a < b"
  using div_le_mono by (fold not_le) blast

lemma exp_gt: "n < b ^ (Suc (nat_log b n))"
proof (induction n rule: induct)
  case (less n)
  then show ?case by simp
next
  case (div n)
  from valid_base and \<open>b \<le> n\<close> have h1: "nat_log b n > 0" by (fastforce simp: nat_log.simps)

  from div.IH have \<open>n div b < b ^ Suc (nat_log b (n div b))\<close> .
  also have "... = b ^ nat_log b n" unfolding nat_log_div Suc_diff_1[OF h1] ..
  also have "... = b ^ Suc (nat_log b n) div b" using valid_base by force
  finally show ?case by (fact div_lt_rev_mono)
qed

lemma (in -) nat_log_less: "nat_log b n < n" if "n > 0" using that
proof (cases "b > 1")
  assume "b > 1"
  then interpret nat_log_base ..
  from \<open>b > 1\<close> have "nat_log b n < b ^ nat_log b n" using power_gt_expt by simp
  also have "... \<le> n" using \<open>n > 0\<close> by (fact exp_le)
  finally show ?thesis .
qed \<comment> \<open>case \<open>b \<le> 1\<close> by\<close> fastforce


lemma (in -) nat_log_le: "nat_log b n \<le> n"
  using nat_log_zero_rev by (cases "n > 0") (blast intro: nat_log_less less_imp_le)+

lemma altdef: "nat_log b n = nat \<lfloor>log b n\<rfloor>" if "n > 0"
proof -
  have "nat_log b n = \<lfloor>log b n\<rfloor>"
  proof (rule floor_unique[symmetric], unfold of_int_of_nat_eq)
    have "nat_log b n = log b (b powr (nat_log b n))" using valid_base by simp
    also have "... \<le> log b n" using that and valid_base
    proof (subst log_le_cancel_iff)
      show "b powr nat_log b n \<le> real n" using that and valid_base using powr_realpow exp_le[OF that] by simp
    qed fastforce+
    finally show "nat_log b n \<le> log b n" .

    have "real n < b ^ (Suc (nat_log b n))" unfolding of_nat_less_iff by (fact exp_gt)
    also have "\<dots> = b powr (real (nat_log b n) + 1)" by (simp add: powr_add powr_realpow nat_log_def)
    finally have "n < b powr (real (nat_log b n) + 1)" .
    then have "log b n < log b \<dots>" using that and valid_base by (subst log_less_cancel_iff) linarith+
    also have "\<dots> = real (nat_log b n) + 1" using valid_base by simp
    finally show "log b n < real (nat_log b n) + 1" by simp
  qed
  then have "nat (int (nat_log b n)) = nat \<lfloor>log b n\<rfloor>" by (fact arg_cong)
  then show ?thesis unfolding nat_int .
qed

lemma cancel: "nat_log b (b^n) = n"
  using valid_base by (induction n) fastforce+

lemmas exp = cancel

lemma eqI:
  assumes "n > 0" "b^k \<le> n" "n < b * b^k"
  shows   "nat_log b n = k"
proof -
  from valid_base have "real b > 0" by simp
  note powr_convert = powr_realpow[OF \<open>real b > 0\<close>]

  from \<open>n > 0\<close> have "nat_log b n = nat \<lfloor>log b n\<rfloor>" by (fact altdef)
  also from \<open>n > 0\<close> and valid_base have "... = nat k"
  proof (subst eq_nat_nat_iff)
    from \<open>n < b * b^k\<close> have "real n < b * b^k" by (fact less_imp_of_nat_less)
    with \<open>b^k \<le> n\<close> have "b powr k \<le> n \<and> n < b powr (k + 1)" unfolding powr_convert by simp
    then have h1: "b powr (int k) \<le> n \<and> n < b powr (int k + 1)"
      unfolding of_int_add of_int_of_nat_eq of_int_1 of_nat_add of_nat_1 .
    with \<open>n > 0\<close> and valid_base show "\<lfloor>log b n\<rfloor> = int k" by (subst floor_log_eq_powr_iff) auto
  qed simp_all
  also have "... = k" by simp
  finally show ?thesis .
qed


lemma exp_m1: "nat_log b (b^n - 1) = n - 1"
proof (cases "n > 0")
  assume "n > 0"
  with valid_base have "b^n - 1 > 0" unfolding zero_less_diff by (rule one_less_power)
  then show ?thesis
  proof (rule eqI)
    from \<open>b > 1\<close> and \<open>n > 0\<close> have "b^(n-1) < b^n" by simp
    also from \<open>b > 1\<close> have "... = Suc (b^n - 1)" by fastforce
    finally show "b^(n-1) \<le> b^n - 1" unfolding less_Suc_eq_le .

    from \<open>b > 1\<close> have "b^n - 1 < b^n" by simp
    also from \<open>n > 0\<close> have "b^n = b * b^(n-1)" by (simp add: power_eq_if)
    finally show "b^n - 1 < b * b^(n-1)" .
  qed
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> fastforce


lemma times_exp:
  assumes "n > 0"
  shows "nat_log b (n * b^k) = nat_log b n + k"
proof (induction k)
  case (Suc k)
  from valid_base and \<open>n > 0\<close> have h1: "n * b^k > 0" by fastforce

  have "n * b^Suc k = b * (n * b^k)" by simp
  then have "nat_log b (n * b ^ Suc k) = nat_log b (b * (n * b^k))" by (fact arg_cong)
  also have "... = nat_log b (n * b^k) + 1" unfolding mult_b[OF h1] by simp
  also have "... = nat_log b n + Suc k" unfolding Suc.IH by simp
  finally show ?case .
qed \<comment> \<open>case \<open>k = 0\<close> by\<close> simp

lemma Suc:
  assumes "n > 0"
  shows "nat_log b (Suc n) = (if Suc n = b ^ nat_log b (Suc n) then Suc (nat_log b n) else nat_log b n)"
    (is "?log (Suc n) = ?rhs")
proof (cases "Suc n = b ^ ?log (Suc n)")
  case True

  have "Suc n \<ge> b"
  proof (rule ccontr)
    assume "\<not> Suc n \<ge> b" hence "Suc n < b" by linarith
    then have "nat_log b (Suc n) = 0" using nat_log_zero_rev by blast
    then have "b ^ nat_log b (Suc n) = 1" by simp
    with True have "Suc n = 1" by simp
    with \<open>n > 0\<close> show False by simp
  qed

  then have "nat_log b (Suc n) > 0" using valid_base using nat_log_zero_rev' by blast

  from True have "?rhs = Suc (nat_log b n)" by (fact if_P)
  also from True have "... = Suc (nat_log b (b ^ nat_log b (Suc n) - 1))" by force
  also have "... = nat_log b (Suc n)" unfolding exp_m1 using \<open>nat_log b (Suc n) > 0\<close> by (fact Suc_diff_1)
  finally show "nat_log b (Suc n) = ?rhs" ..
next
  case False
  then have req: "?rhs = nat_log b n" by (fact if_not_P)
  also have "... = nat_log b (Suc n)"
  proof (intro eqI[symmetric])
    show "Suc n > 0" ..
    from \<open>n > 0\<close> have "n \<ge> b ^ nat_log b n" by (fact exp_le)
    then show "Suc n \<ge> b ^ nat_log b n" by (fact le_SucI)

    have "Suc n > b ^ nat_log b (Suc n)" using exp_le False by (intro le_neq_trans) (blast, argo)
    then have "n \<ge> b ^ nat_log b (Suc n)" by simp
    with nat_log_mono have "nat_log b n \<ge> nat_log b (b ^ (nat_log b (Suc n)))" ..
    then have "nat_log b n \<ge> nat_log b (Suc n)" unfolding cancel .

    moreover have "nat_log b n \<le> nat_log b (Suc n)" by (fact nat_log_Suc_ge)
    ultimately have deq: "nat_log b (Suc n) = nat_log b n" by (fact le_antisym)
    from exp_gt[of "Suc n"] show "Suc n < b * b ^ nat_log b n" unfolding deq power_Suc .
  qed
  finally show ?thesis ..
qed

corollary add1_le: "nat_log b (n + 1) \<le> nat_log b n + 1"
proof (cases "n > 0", unfold not_gr_zero)
  assume "n > 0" thus ?thesis by (fold Suc_eq_plus1, subst Suc) simp_all next
  assume "n = 0" thus ?thesis using valid_base by force
qed


subsubsection\<open>Discrete Ceiling Log\<close>

definition (in -) nat_log_ceil :: "nat \<Rightarrow> nat \<Rightarrow> nat" \<comment> \<open>\<open>\<lceil>log\<^sub>2 n\<rceil>\<close> over the natural numbers\<close>
  where "nat_log_ceil b n \<equiv> nat_log b (n-1) + 1"

lemma (in -) "nat_log_ceil b 0 = 1" unfolding nat_log_ceil_def by simp

lemma ceil_exp[simp]: "nat_log_ceil b (b^n) = n" if "n > 0"
  using that unfolding nat_log_ceil_def by (subst exp_m1) fastforce+

lemma ceil_gt_0[simp]: "nat_log_ceil b n > 0" unfolding nat_log_ceil_def by force

lemma ceil_eq1: "n \<le> b \<Longrightarrow> nat_log_ceil b n = 1" unfolding nat_log_ceil_def
  using valid_base by (subst nat_log_0(2)) linarith+

lemma ceil_le: "0 < n \<Longrightarrow> nat_log_ceil b n \<le> n"
proof -
  assume "n > 0"
  have "nat_log b (n-1) \<le> n-1" by (rule nat_log_le)
  then have "nat_log_ceil b n \<le> n-1 + 1" by (unfold nat_log_ceil_def add_le_cancel_right)
  also have "... = n" using \<open>n > 0\<close> by simp
  finally show "nat_log_ceil b n \<le> n" .
qed

lemma le_nat_log_ceil[simp]: "nat_log b n \<le> nat_log_ceil b n"
proof (cases "n > 0")
  assume "n > 0"
  then have n_split: "n - 1 + 1 = n" by simp
  have "nat_log b n = nat_log b (n - 1 + 1)" unfolding n_split ..
  also have "... \<le> nat_log b (n - 1) + 1"  by (rule add1_le)
  finally show "nat_log b n \<le> nat_log_ceil b n" unfolding nat_log_ceil_def .
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp

lemma ceil_le_nat_log_p1: "nat_log_ceil b n \<le> nat_log b n + 1"
proof -
  have "nat_log_ceil b n = nat_log b (n - 1) + 1" unfolding nat_log_ceil_def ..
  also have "... \<le> nat_log b n + 1" unfolding add_le_cancel_right by (intro nat_log_le_iff diff_le_self)
  finally show "nat_log_ceil b n \<le> nat_log b n + 1" .
qed

lemma ceil_mono: "mono (nat_log_ceil b)"
  unfolding nat_log_ceil_def by (intro monoI add_le_mono1 nat_log_le_iff diff_le_mono)


lemma power_decompose:
  assumes "n > 0"
  defines "k \<equiv> nat_log b n"
  defines "m \<equiv> n - b^k"
  shows "n = b^k + m" and "m < b^(k+1) - b^k"
proof -
  from \<open>n > 0\<close> have le: "b ^ k \<le> n" unfolding k_def by (fact exp_le)
  then show "n = b^k + m" unfolding m_def by (rule le_add_diff_inverse[symmetric])

  from exp_gt have "n < b^(k+1)" unfolding k_def by force
  with le show "m < b^(k+1) - b^k" unfolding m_def by (intro diff_less_mono)
qed

lemma power_decompose':
  assumes "n > 0"
  obtains k m :: nat
  where "n = b^k + m" and "m < b^(k+1) - b^k"
  using power_decompose[OF \<open>n > 0\<close>] by blast


lemma log_eq1:
  assumes "m < b^(k+1) - b^k"
  shows "nat_log b (b^k + m) = k"
proof (intro eqI)
  from \<open>m < b^(k+1) - b^k\<close> have "b^k + m < b^k + (b^(k+1) - b^k)" by (fact add_strict_left_mono)
  also have "... = b * b^k" using valid_base by force
  finally show "b^k + m < b * b^k" .
qed (use assms in auto)

lemma log_eq2:
  fixes k m :: nat
  assumes "m \<ge> 1" and "m < b^(k+1) - b^k"
  shows "nat \<lceil>log b (b^k + m)\<rceil> = k + 1"
proof -
  let ?n = "b^k+m"
  from \<open>m \<ge> 1\<close> have "k < log b (b^k + m)" using valid_base by (intro less_log_of_power) fastforce+
  moreover have "log b (b^k + m) \<le> k+1" using valid_base
  proof (intro log_of_power_le)
    from \<open>m < b^(k+1) - b^k\<close>
    have "b ^ k + m \<le> b ^ (k + 1)" by linarith
    then show "real (b ^ k + m) \<le> real b ^ (k + 1)" by (fold of_nat_power) (fact of_nat_mono)
  qed force+
  ultimately show ?thesis by linarith
qed

lemma ceil_altdef:
  assumes "n > 1"
  shows "nat_log_ceil b n = nat \<lceil>log b n\<rceil>"
proof (cases "n \<ge> b")
  assume "\<not> n \<ge> b"
  then have "n \<le> b" by linarith
  then have "nat_log_ceil b n = 1" by (fact ceil_eq1)
  also have "... = nat \<lceil>log b n\<rceil>"
  proof -
    from \<open>n > 1\<close> have "real n > 0" by linarith
    from valid_base have "real b > 1" by linarith
    note h1 = \<open>real b > 1\<close> \<open>real n > 0\<close>
    note h2 = zero_less_log_cancel_iff[OF h1] log_le_one_cancel_iff[OF h1]

    from \<open>n > 1\<close> and \<open>n \<le> b\<close> have "\<lceil>log b n\<rceil> = 1" by (force intro: ceiling_unique simp: h2)
    then show ?thesis by simp
  qed
  finally show ?thesis .
next
  assume "n \<ge> b"
  from assms valid_base have "n > 0" by simp
  with power_decompose' obtain k m where km_def: "n = b^k + m" "m < b^(k+1) - b^k" .

  show "nat_log_ceil b n = nat \<lceil>log b n\<rceil>" unfolding nat_log_ceil_def
  proof (cases "m = 0")
    case True
    then have k_def: "n = b^k" using \<open>n = b^k + m\<close> by simp

    have "nat_log b (n-1) + 1 = (k-1) + 1" unfolding add_right_cancel k_def by (rule exp_m1)
    also have "... = k" using valid_base
    proof (intro le_add_diff_inverse2 power_le_imp_le_exp)
      show "b ^ 1 \<le> b ^ k" using \<open>n \<ge> b\<close> unfolding k_def by simp
    qed
    also have "... = nat_log b (b^k)" using cancel ..
    also have "... = nat \<lceil>log b (b^k)\<rceil>" using valid_base by (subst altdef) force+
    also have "... = nat \<lceil>log b n\<rceil>" unfolding k_def ..
    finally show "nat_log b (n-1) + 1 = nat \<lceil>log b n\<rceil>" .
  next
    case False
    then have "1 \<le> m" by simp_all
    from \<open>m < b^(k+1) - b^k\<close> have "m-1 < b^(k+1) - b^k" by (rule less_imp_diff_less)

    have "nat_log b (n-1) = nat_log b (b^k + (m-1))" unfolding km_def
      using \<open>1 \<le> m\<close> by (subst diff_add_assoc) simp_all
    also have "... = k" using \<open>m-1 < b^(k+1) - b^k\<close> by (rule log_eq1)
    finally have "nat_log b (n-1) + 1 = k + 1" unfolding add_right_cancel .
    also have "... = nat \<lceil>log b n\<rceil>" unfolding km_def
      using \<open>1 \<le> m\<close> and \<open>m < b^(k+1) - b^k\<close> by (rule log_eq2[symmetric])
    finally show "nat_log b (n-1) + 1 = nat \<lceil>log b n\<rceil>" .
  qed
qed

end

end