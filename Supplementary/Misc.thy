chapter\<open>Supplementary Material\<close>

text\<open>Extends existing sessions with helpful lemmas and definitions.\<close>

section\<open>Misc\<close>

theory Misc
  imports Complex_Main
begin


text\<open>Extends \<^theory>\<open>HOL.Fun\<close>, \<^theory>\<open>HOL.Set\<close>, and \<^theory>\<open>HOL.Orderings\<close>.\<close>


lemma Ball_transferE[elim?]:
  assumes "\<forall>x\<in>A. P x"
    and "\<And>x. x\<in>A \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows "\<forall>x\<in>A. Q x"
  using assms by blast

lemma cond_All_mono:
  assumes "\<forall>i. P i \<longrightarrow> Q i"
    and "\<And>i. P i \<Longrightarrow> Q i \<Longrightarrow> R i"
  shows "\<forall>i. P i \<longrightarrow> R i"
proof (intro allI impI)
  fix i
  assume "P i"
  with \<open>\<forall>i. P i \<longrightarrow> Q i\<close> have "Q i" by blast
  with assms(2) and \<open>P i\<close> show "R i" .
qed


lemma inj_altdef: "inj f \<longleftrightarrow> (\<forall>a b. a \<noteq> b \<longrightarrow> f a \<noteq> f b)" unfolding inj_def by blast


lemma If_If[simp]: "If P (If P a x) b = If P a b" by presburger

lemma ifI[case_names True False]:
  assumes "c \<Longrightarrow> P a"
    and "\<not>c \<Longrightarrow> P b"
  shows "P (If c a b)"
  using assms by force


lemma Max_atLeastAtMost_nat:
  fixes x y :: nat
  assumes "x \<le> y"
  shows "Max {x..y} = y"
  using assms by (intro Max_eqI) auto

lemma Max_atLeastLessThan_nat:
  fixes x y :: nat
  assumes "x < y"
  shows "Max {x..<y} = y-1"
  using assms
proof (induction y)
  case (Suc y)
  from \<open>x < Suc y\<close> have "x \<le> y" by auto
  then show ?case unfolding atLeastLessThanSuc_atLeastAtMost diff_Suc_1
    by (rule Max_atLeastAtMost_nat)
qed blast

lemma inj_imp_inj_on[dest]: "inj f \<Longrightarrow> inj_on f A" by (simp add: inj_on_def)


lemma inv_into_onto: "inj_on f A \<Longrightarrow> inv_into A f ` f ` A = A" by simp

lemma bij_betw_obtain_preimage:
  assumes "bij_betw f A B" and "b \<in> B"
  obtains a where "a\<in>A" and "f a = b"
  using assms by (meson bij_betw_iff_bijections)

(* Suppl_Set ? *)
lemma singleton_image[simp]: "f ` {x} = {f x}" by blast

lemma image_Collect_compose: "f ` {g x | x. P x} = {f (g x) | x. P x}" by blast

lemma map_image[intro]: "set xs \<subseteq> A \<Longrightarrow> set (map g xs) \<subseteq> g ` A"
  unfolding set_map by (fact image_mono)

lemma finite_imp_inj_to_nat_fix_one:
  fixes A::"'a set" and x::'a and y::nat
  assumes "finite A"
  shows "\<exists>g. inj_on g A \<and> g x = y"
proof -
  from finite_imp_inj_to_nat_seg[OF assms]
  obtain f::"'a \<Rightarrow> nat" where "inj_on f A" by fast

  define g where "g = (\<lambda>x. f x + y + 1)(x := y)"
  from g_def have 1: "g x' = y \<Longrightarrow> x' = x" for x'
    by (cases "x' = x") simp+
  from g_def have 2: "a \<in> A \<Longrightarrow> a \<noteq> x \<Longrightarrow> g a = f a + y + 1" for a
    by simp

  have "inj_on g A" proof (intro inj_onI)
    fix a1 a2
    assume "a1 \<in> A" "a2 \<in> A" "g a1 = g a2"
    thus "a1 = a2" proof (cases "a1 = x")
      case True
      then have "g a1 = y" unfolding g_def by simp
      with 1[of a2] \<open>a1 = x\<close> \<open>g a1 = g a2\<close> show "a1 = a2" by simp
    next
      case False
      have "a2 \<noteq> x" proof (rule ccontr)
        assume "\<not> a2 \<noteq> x"
        hence "g a2 = y" unfolding g_def by simp
        with \<open>g a1 = g a2\<close> have "a1 = x" using 1[of a1] by simp
        thus False using \<open>a1 \<noteq> x\<close> by simp
      qed
      with \<open>a2 \<in> A\<close> 2 have "g a2 = f a2 + y + 1" by simp
      moreover have "g a1 = f a1 + y + 1" using \<open>a1 \<noteq> x\<close> \<open>a1 \<in> A\<close> 2 by simp
      ultimately have "f a1 = f a2" using \<open>g a1 = g a2\<close> by force
      thus "a1 = a2" using \<open>inj_on f A\<close> \<open>a1 \<in> A\<close> \<open>a2 \<in> A\<close> by (elim inj_onD)
    qed
  qed
  moreover have "g x = y" unfolding g_def fun_upd_same ..
  ultimately show ?thesis by blast
qed

(* Suppl_Orderings ? *)
lemma nat_strict_mono_greatest:
  fixes f::"nat \<Rightarrow> nat" and N::nat
  assumes "strict_mono f" "f 0 \<le> N"
  obtains n where "f n \<le> N" and "\<forall>m. f m \<le> N \<longrightarrow> m \<le> n"
proof -
  define M where "M \<equiv> {m. f m \<le> N}"
  define n where "n = Max M"

  from \<open>strict_mono f\<close> have "\<And>n. n \<le> f n" by (rule strict_mono_imp_increasing)
  hence "finite M" using M_def finite_less_ub by simp
  moreover from M_def \<open>f 0 \<le> N\<close> have "M \<noteq> {}" by auto
  ultimately have "n \<in> M" unfolding n_def using Max_in[of M] by simp

  then have "f n \<le> N" using n_def M_def by simp
  moreover have "\<forall>m. f m \<le> N \<longrightarrow> m \<le> n"
    using Max_ge \<open>finite M\<close> n_def M_def by blast
  ultimately show thesis using that by simp
qed

lemma max_cases:
  assumes "P a" and "P b"
  shows "P (max a b)"
  using assms unfolding max_def by simp

lemma max_nat: "max a b = a + (b - a)" for a b :: nat
  using nat_le_linear[of a b] by fastforce

lemma fold_max_triv: "fold max xs x \<ge> x" for x :: "'a :: linorder" and xs
  by (fold Max.set_eq_fold) simp

(* Suppl_Nat.thy ? *)
lemma funpow_induct: "P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> P (f x)) \<Longrightarrow> P ((f^^n) x)" by (induction n) auto

lemma funpow_fixpoint: "f x = x \<Longrightarrow> (f^^n) x = x" by (rule funpow_induct) auto


lemma isl_not_def: "\<not> isl x \<longleftrightarrow> (\<exists>x2. x = Inr x2)" \<comment> \<open>analogous to @{thm isl_def}\<close>
  by (cases x) auto

lemma case_sum_cases[case_names Inl Inr]:
  assumes "\<And>l. x = Inl l \<Longrightarrow> P (f l)"
    and "\<And>r. x = Inr r \<Longrightarrow> P (g r)"
  shows "P (case x of Inl l \<Rightarrow> f l | Inr r \<Rightarrow> g r)"
  using assms using sum.split_sel by blast

lemma Least_natI [intro]:
  fixes n :: nat and P :: "nat \<Rightarrow> bool"
  assumes "P n" and "\<And>m. m < n \<Longrightarrow> \<not>P m"
  shows "(LEAST m. P m) = n"
  unfolding Least_def using assms by (metis LeastI Least_def nat_neq_iff not_less_Least)

lemma Least_nat_monoI:
  fixes n :: nat and P :: "nat \<Rightarrow> bool"
  assumes "P n" and "n > 0 \<Longrightarrow> \<not>P (n - 1)" and "\<And>n. P n \<Longrightarrow> P (Suc n)"
  shows "(LEAST n. P n) = n"
  apply (rule Least_natI)
   apply fact
proof
  fix m :: nat
  assume a1: "m < n" and a2: "P m"
  have 1: "m' \<ge> m \<Longrightarrow> P m'" for m' :: nat
  proof (induction m' rule: nat_induct_at_least)
    case base
    then show ?case by fact
  next
    case (Suc n)
    show ?case using Suc(2) by (rule assms(3))
  qed
  have 2: "P (n - 1)" using a1 1 [of "n - 1"] by linarith
  show False apply (cases "n > 0")
     apply (drule assms(2))
    using 2 apply simp
    using a1 by simp
qed

lemma nat_gr0_obtain_prev:
  assumes "(n::nat) > 0"
  obtains nm1 :: nat where "Suc nm1 = n" using assms gr0_implies_Suc by blast

lemma n_gt_0_eq_Suc_nat: "(n > 0 \<Longrightarrow> P) \<equiv> (\<And>nat. n = Suc nat \<Longrightarrow> P)"
  apply standard
   apply auto
  by (rule lessE)

lemma suc_is_gt: "n = Suc m \<Longrightarrow> n > m"
  by simp

lemma suc_is_ge: "n = Suc m \<Longrightarrow> n \<ge> m"
  by simp

lemma minus_mod_div [simp]: "((x::nat) - x mod k) div k = x div k"
  by (simp add: minus_mod_eq_mult_div)

lemma hd_cons_id [simp]: "hd \<circ> (\<lambda>x. [x]) = id"
  by auto

lemma map_cons_hd_id [simp]: "set w \<subseteq> {[True], [False]} \<Longrightarrow>
                              (map ((\<lambda>x. [x]) \<circ> hd) w) = w"
  by (induction w) auto

lemma iff_classicalI: "(A \<Longrightarrow> B) \<Longrightarrow> (\<not>A \<Longrightarrow> \<not>B) \<Longrightarrow> A \<longleftrightarrow> B"
  by blast

lemma Least_smaller_exists: "P (LEAST x::nat. P x) \<Longrightarrow>
  (LEAST x. P x) > 0 \<Longrightarrow> \<exists>x'<(LEAST x. P x). \<not>P x'"
  by auto

lemma Least_eqD [dest]: "(LEAST x::nat. P x) = y \<Longrightarrow> P x \<Longrightarrow> P y"
  unfolding Least_def apply auto
  by (metis LeastI Least_def)

lemma set_replicate_iff: "set (replicate n x) = {x} \<longleftrightarrow> n > 0"
  by auto

lemma x_d2_m2_iff1: "(x::nat) div 2 * 2 = x \<longleftrightarrow> x mod 2 = 0"
  by presburger

lemma x_d2_m2_iff2: "(x::nat) div 2 * 2 = x \<longleftrightarrow> even x"
  by presburger

lemma min_eqI: "((n::('a::linorder)) \<le> m \<Longrightarrow> n = x) \<Longrightarrow>
                (m \<le> n \<Longrightarrow> m = x) \<Longrightarrow> min n m = x"
  by fastforce

lemma max_eqI: "((n::('a::linorder)) \<le> m \<Longrightarrow> m = x) \<Longrightarrow>
                (m \<le> n \<Longrightarrow> n = x) \<Longrightarrow> max n m = x"
  by fastforce

lemma Least_conj:
  fixes n :: nat
  assumes P_sat: "P n" and Q_sat: "Q n"
  shows Least_conj_P: "P (LEAST n. P n \<and> Q n)" and
        Least_conj_Q: "Q (LEAST n. P n \<and> Q n)"
    using assms by (metis (no_types, lifting) LeastI_ex)+

lemma Least_conj_ge:
  fixes n :: nat
  assumes P_sat: "P n" and Q_sat: "Q n"
  shows Least_conj_ge_P: "(LEAST n. P n) \<le> (LEAST n. P n \<and> Q n)" and
        Least_conj_ge_Q: "(LEAST n. Q n) \<le> (LEAST n. P n \<and> Q n)"
  using assms by (metis (no_types, lifting) LeastI Least_le)+

lemma Least_conj_ge_ex:
  assumes PQ_ex: "\<exists>n::nat. P n \<and> Q n"
  shows Least_conj_ge_P_ex: "(LEAST n. P n) \<le> (LEAST n. P n \<and> Q n)" and
        Least_conj_ge_Q_ex: "(LEAST n. Q n) \<le> (LEAST n. P n \<and> Q n)"
  using assms Least_conj_ge by meson+

lemma Least_ge [simp]: "(LEAST n::('a::linorder). n \<ge> m) = m"
  by (simp add: Least_equality)

lemma Greatest_le [simp]: "(GREATEST n::('a::linorder). n \<le> m) = m"
  by (simp add: Greatest_equality)

lemma nat_semiring_1_powadd:
  fixes m n p :: nat
  shows "(of_nat (((+) m ^^ p) n)::('a::semiring_1)) =
         (((+) (of_nat m) ^^ p) (of_nat n))"
  by (induction p) simp_all

lemma Alm_all_natI: "(\<And>n::nat. n \<ge> n\<^sub>0 \<Longrightarrow> P n) \<Longrightarrow> \<forall>\<^sub>\<infinity>n. P n"
  unfolding eventually_cofinite by (metis finite_nat_set_iff_bounded_le
      linorder_not_le mem_Collect_eq order_le_less)

lemma Alm_all_finiteI:
  assumes finite_P: "finite {l::'a. P l}"
  shows "\<forall>\<^sub>\<infinity>l::'a. P l \<longrightarrow> Q l"
proof (unfold eventually_cofinite, auto)
  show "finite {x. P x \<and> \<not> Q x}" using finite_P by simp
qed

lemma Alm_all_finite_listI:
  assumes bounded: "\<And>l::'a list. set l \<subseteq> S \<Longrightarrow> length l \<ge> l\<^sub>0 \<Longrightarrow> P l" and
          finite_S: "finite S"
  shows "\<forall>\<^sub>\<infinity>l. set l \<subseteq> S \<longrightarrow> P l"
proof (unfold eventually_cofinite, auto)
  have "finite {l. set l \<subseteq> S \<and> length l < l\<^sub>0}"
  proof -
    have length_eq: "\<And>n::nat. card {l. set l \<subseteq> S \<and> length l = n} = (card S) ^ n"
      using card_lists_length_eq finite_S by blast
    have 1: "\<And>n::nat. card {l. set l \<subseteq> S \<and> length l < n} =
              sum (\<lambda>n. card S ^ n) {0..<n}"
    proof -
      fix n :: nat
      show "card {l. set l \<subseteq> S \<and> length l < n} = sum ((^) (card S)) {0..<n}"
        apply (induction n)
      proof auto
        fix n :: nat
        assume a1: "card {l. set l \<subseteq> S \<and> length l < n} = sum ((^) (card S)) {0..<n}"
        have union: "{l. set l \<subseteq> S \<and> length l < Suc n} =
                     {l. set l \<subseteq> S \<and> length l < n} \<union> {l. set l \<subseteq> S \<and> length l = n}"
          by auto
        have inter: "{l. set l \<subseteq> S \<and> length l < n} \<inter> {l. set l \<subseteq> S \<and> length l = n} =
                     {}" by auto
        have "finite {l. set l \<subseteq> S \<and> length l = n}"
          by (rule finite_lists_length_eq) (fact finite_S)
        moreover have "finite {l. set l \<subseteq> S \<and> length l < n}"
        proof -
          have "card {l. set l \<subseteq> S \<and> length l < n} = 0 \<Longrightarrow>
                finite {l. set l \<subseteq> S \<and> length l < n}"
            unfolding a1 by fastforce
          thus "finite {l. set l \<subseteq> S \<and> length l < n}" by (meson card_eq_0_iff)
        qed
        ultimately show "card {l. set l \<subseteq> S \<and> length l < Suc n} =
              sum ((^) (card S)) {0..<n} + card S ^ n" unfolding union using a1 inter
          by (simp add: card_Un_disjoint length_eq)
      qed
    qed
    moreover have "\<And>n::nat. card {l. set l \<subseteq> S \<and> length l < n} > 0 \<or>
                   {l. set l \<subseteq> S \<and> length l < n} = {}"
    proof auto
      fix n :: nat and l :: "'a list"
      assume a1: "card {l. set l \<subseteq> S \<and> length l < n} = 0" and a2: "set l \<subseteq> S" and
             a3: "length l < n"
      have 2: "sum (\<lambda>n. card S ^ n) {0..<n} = 0 \<longleftrightarrow> n = 0" by auto
      have "card {l. set l \<subseteq> S \<and> length l < n} = 0 \<Longrightarrow> n = 0" unfolding 1 2 .
      thus False using a1 a3 by simp
    qed
    ultimately show "finite {l. set l \<subseteq> S \<and> length l < l\<^sub>0}"
      by (metis (mono_tags) card.infinite finite.emptyI lessI not_less_eq)
  qed
  thus "finite {l. set l \<subseteq> S \<and> \<not> P l}" using bounded
    by (smt (verit, best) Collect_mono_iff finite_subset leI)
qed

lemma Alm_all_listI:
  assumes "\<And>l::('a::finite) list. length l \<ge> l\<^sub>0 \<Longrightarrow> P l"
  shows "\<forall>\<^sub>\<infinity>l. P l"
  apply (rule Alm_all_finite_listI [where S=UNIV, simplified])
  using assms by auto

lemma funpow_m1_eq: "n > 0 \<Longrightarrow> f \<circ> f ^^ (n - Suc 0) = f ^^ n"
  by (metis Suc_pred funpow.simps(2))

lemma even_nat_induct [consumes 1, case_names 0 step]:
  fixes n :: nat and P :: "nat \<Rightarrow> bool"
  assumes even_n: "even n" and
          base: "P 0" and
          step: "\<And>n. even n \<Longrightarrow> P n \<Longrightarrow> P (Suc (Suc n))"
        shows "P n"
  using even_n apply (induction n rule: full_nat_induct)
proof -
  fix n :: nat
  assume a1: "\<forall>m. Suc m \<le> n \<longrightarrow> even m \<longrightarrow> P m" and
         a2: "even n"
  show "P n"
    apply (cases n)
     apply (simp add: base)
  proof -
    fix n' :: nat
    assume a3: "n = Suc n'"
    hence "odd n'" using a2 by simp
    then obtain m :: nat where n_def: "n = Suc (Suc m)"
      by (metis a3 odd_Suc_minus_one)
    have 1: "even m" using a2 unfolding n_def by simp
    have 2: "P m" using n_def a1 1 by simp
    show "P n"
      unfolding n_def apply (rule step)
      by fact+
  qed
qed

lemma odd_nat_induct [consumes 1, case_names 1 step]:
  fixes n :: nat and P :: "nat \<Rightarrow> bool"
  assumes even_n: "odd n" and
          base: "P (Suc 0)" and
          step: "\<And>n. odd n \<Longrightarrow> P n \<Longrightarrow> P (Suc (Suc n))"
        shows "P n"
  using even_n apply (induction n rule: full_nat_induct)
proof -
  fix n :: nat
  assume a1: "\<forall>m. Suc m \<le> n \<longrightarrow> odd m \<longrightarrow> P m" and
         a2: "odd n"
  show "P n"
    apply (cases n)
    using a2 apply simp
  proof -
    fix n' :: nat
    assume a3: "n = Suc n'"
    show "P n"
      unfolding a3 apply (cases n')
       apply (auto simp add: base)
    proof -
      fix m :: nat
      assume a4: "n' = Suc m"
      have 1: "n = Suc (Suc m)" using a3 a4 by simp
      have 2: "odd m" using a2 unfolding 1 by simp
      have 3: "P m" using a1 a3 a4 2 by simp
      show "P (Suc (Suc m))"
        apply (rule step)
        by fact+
    qed
  qed
qed

lemma nat_pow_div_mult_eq [simp]: "n > 0 \<Longrightarrow> (((b::nat) ^ n) div b) * b = b ^ n"
  by simp

lemma k_eq_div_iff: "d \<ge> 2 \<Longrightarrow> (k::nat) = k div d \<longleftrightarrow> k = 0"
  by (metis bits_1_div_2 div_eq_dividend_iff div_greater_zero_iff div_less
      dual_order.strict_trans1 less_2_cases_iff linorder_not_le)

lemma k_eq_half_iff: "(k::nat) = k div 2 \<longleftrightarrow> k = 0"
  by (rule k_eq_div_iff) standard

lemma bij_betw_empty_empty [intro, simp]: "bij_betw f {} {}"
  unfolding bij_betw_def by simp

lemma odd_n_div_mult2 [simp]: "odd n \<Longrightarrow> n div 2 * 2 = n - 1"
  by (metis minus_mod_eq_div_mult parity_cases)

lemma nat_div_pow2_distribute: "(n::nat) < 2^k \<Longrightarrow>
  (x * 2^k + n) div 2^l = x * 2^k div 2^l + n div 2^l"
proof (induction l)
  case 0
  then show ?case by simp
next
  case IH: (Suc l)
  hence "(x * 2 ^ k + n) div 2 ^ l = x * 2 ^ k div 2 ^ l + n div 2 ^ l" .
  hence "(x * 2 ^ k + n) div 2 ^ Suc l = (x * 2 ^ k div 2 ^ l + n div 2 ^ l) div 2"
    by (metis div_mult2_eq power_Suc2)
  also have "... = x * 2 ^ k div 2 ^ Suc l + n div 2 ^ Suc l"
  proof (cases "n div 2 ^ l = 0")
    case True
    then show ?thesis apply simp
      by (metis (no_types, opaque_lifting) add.commute comm_monoid_add_class.add_0 div_0
          div_mult2_eq mult.commute)
  next
    case False
    hence "2^l \<le> n" by (meson div_less leI)
    hence "l < k" using IH(2)
      by (meson dual_order.strict_trans2 less_2_cases_iff nat_power_less_imp_less)
    then show ?thesis
      by (metis calculation div_plus_div_distrib_dvd_left dvd_mult dvd_power_iff_le
          le_refl less_eq_Suc_le)
  qed
  finally show ?case .
qed

lemma permutation_with_fixed_element:
  fixes S :: "'a set" and x y :: 'a
  assumes "x \<in> S" and "y \<in> S"
  obtains f :: "'a \<Rightarrow> 'a" where "bij_betw f S S" and "f x = y" and "f y = x" and
    "\<And>z. z \<noteq> x \<Longrightarrow> z \<noteq> y \<Longrightarrow> f z = z"
proof
  define f :: "'a \<Rightarrow> 'a" where
    "\<And>s. f s \<equiv> if s = x then y else if s = y then x else s"
  show "bij_betw f S S"
    unfolding bij_betw_def apply auto
  proof
    fix a b :: 'a
    assume a1: "a \<in> S" and a2: "b \<in> S" and a3: "f a = f b"
    thus "a = b"
      apply (cases "a = x")
      unfolding f_def apply auto
       apply (cases "b = x")
        apply auto
       apply (cases "b = y")
        apply auto
      apply (cases "a = y")
       apply auto
       apply (cases "b = x")
        apply auto
       apply (cases "b = y")
        apply auto
      apply (cases "y = x")
      by simp_all
  next
    fix a :: 'a
    assume a1: "a \<in> S"
    thus "f a \<in> S" unfolding f_def apply auto
       apply (rule assms(1))
      by (rule assms(2))
  next
    fix a :: 'a
    assume a1: "a \<in> S"
    thus "a \<in> f ` S" unfolding f_def apply auto
      using assms(2) apply blast
      using assms(1) by blast
  qed
  show "f x = y" unfolding f_def by simp
  show "(if y = x then y else if y = y then x else y) = x" by argo
  show "\<And>z. z \<noteq> x \<Longrightarrow> z \<noteq> y \<Longrightarrow> (if z = x then y else if z = y then x else z) = z" by argo
qed

lemma reals_ceil_floor_eq_iff: "(x::real) \<notin> \<int> \<Longrightarrow> (y::real) \<notin> \<int> \<Longrightarrow> \<lceil>x\<rceil> = \<lceil>y\<rceil> \<longleftrightarrow> \<lfloor>x\<rfloor> = \<lfloor>y\<rfloor>"
  by (smt (verit) Ints_of_int ceiling_altdef)

lemma reals_floors_lt_ex_exact: "\<lfloor>(x::real)\<rfloor> < \<lfloor>x + (y::real)\<rfloor> \<Longrightarrow>
                                 (\<exists>(z::real)\<le>y. z \<ge> 0 \<and> \<lfloor>x + y\<rfloor> = x + z)"
  unfolding floor_less_iff
proof -
  assume a1: "x < real_of_int \<lfloor>x + y\<rfloor>"
  hence 1: "y > 0" by linarith
  have "real_of_int \<lfloor>x + y\<rfloor> = x + (\<lfloor>x + y\<rfloor> - x)" by simp
  moreover have "\<lfloor>x + y\<rfloor> - x \<ge> 0" using a1 by simp
  moreover have "\<lfloor>x + y\<rfloor> - x \<le> y" by linarith
  ultimately show "\<exists>z\<le>y. 0 \<le> z \<and> real_of_int \<lfloor>x + y\<rfloor> = x + z" by blast
qed

lemma reals_ceiling_lt_iff: "x \<notin> \<int> \<Longrightarrow> y \<notin> \<int> \<Longrightarrow> \<lceil>(x::real)\<rceil> < \<lceil>(y::real)\<rceil> \<longleftrightarrow> \<lfloor>x\<rfloor> < \<lfloor>y\<rfloor>"
  unfolding ceiling_altdef apply auto
  by (metis Ints_of_int)+

lemma real_div_nat_in_int: "y > 0 \<Longrightarrow> (x::real) / real y \<in> \<int> \<Longrightarrow> x \<in> \<int>"
proof -
  assume a1: "y > 0" and a2: "x / real y \<in> \<int>"
  obtain z :: int where "x / real y = z" using a2 by (rule Ints_cases)
  hence [symmetric]: "z * real y = x" using a1 by (simp add: nonzero_divide_eq_eq)
  thus "x \<in> \<int>" by simp
qed

lemma real_sum_in_Ints: "((x::real) + (y::real)) \<in> \<int> \<Longrightarrow> x \<in> \<int> \<longleftrightarrow> y \<in> \<int>"
  by (smt (verit) Ints_add minus_in_Ints_iff)

lemma ceiling_div_is_floor_div: "\<lceil>real (x::nat) / real (y::nat)\<rceil> =
                                 \<lfloor>(real x + y - 1) / real y\<rfloor>"
proof (induction x)
  case 0
  then show ?case apply simp
    by (metis (no_types, lifting) div_self floor_diff_one floor_divide_real_eq_div
        floor_of_nat nonneg1_imp_zdiv_pos_iff of_int_of_nat_eq of_nat_0_le_iff
        zdiv_eq_0_iff zero_less_one zle_diff1_eq)
next
  case (Suc x)
  have 1: "\<lfloor>(real x + real y) / real y\<rfloor> = (x + y) div y"
    by (metis floor_divide_of_nat_eq of_nat_add)
  have 2: "\<lfloor>(real x + real y - 1) / real y\<rfloor> = (x + y - 1) div y"
    by (smt (verit, ccfv_threshold) One_nat_def add.commute add.commute ceiling_diff_one
        ceiling_one div_by_0 div_by_0 div_by_Suc_0 div_greater_zero_iff floor_diff_one
        floor_divide_of_nat_eq floor_one numeral_code(1) of_nat_0 of_nat_0_less_iff of_nat_1
        of_nat_add of_nat_diff of_nat_le_0_iff trans_less_add2)
  have 3: "(1 + real x) / real y = real_of_int \<lfloor>(1 + real x) / real y\<rfloor> \<Longrightarrow>
           (1 + real x) / real y \<in> \<int>" by (metis Ints_of_int)
  have 4: "(1 + real x) / real y \<noteq> real_of_int \<lfloor>(1 + real x) / real y\<rfloor> \<Longrightarrow>
           (1 + real x) / real y > real_of_int \<lfloor>(1 + real x) / real y\<rfloor>" by linarith
  have 5: "real x / real y \<noteq> real_of_int \<lfloor>real x / real y\<rfloor> \<Longrightarrow>
           real x / real y > real_of_int \<lfloor>real x / real y\<rfloor>" by linarith
  have 6: "y > 0 \<Longrightarrow> (real x + real y - 1) / real y = (real x - 1) / real y + 1"
    by (metis Euclidean_Rings.div_eq_0_iff[of y "0"]
        add_divide_distrib[of "of_nat x - 1" "of_nat y" "of_nat y"]
        diff_minus_eq_add[of "of_nat x - 1" "of_nat y"]
        diff_minus_eq_add[of "of_nat x" "of_nat y"]
        diff_right_commute[of "of_nat x" "1" "- of_nat y"] div_eq_dividend_iff[of y "0"]
        of_nat_0_eq_iff[of y] one_eq_divide_iff[of "of_nat y" "of_nat y"] one_neq_zero)
  show ?case using Suc
    unfolding ceiling_altdef apply auto
     apply (cases "real x / real y = real_of_int \<lfloor>real x / real y\<rfloor>")
      apply auto
    apply (smt (verit, ccfv_SIG) 1 2 One_nat_def add_divide_distrib floor_correct floor_eq2
        of_int_of_nat_eq real_of_int_floor_add_one_gt)
     apply (cases "y = 0")
      apply auto
     apply (drule 3)
    apply (smt (verit) 1 2 One_nat_def Suc add_implies_diff ceiling_eq_iff div_if
        divide_less_cancel floor_divide_of_nat_eq floor_eq_iff int_ops(2) int_plus
        not_add_less2 of_int_floor of_nat_less_0_iff plus_1_eq_Suc)
    apply (cases "real x / real y = real_of_int \<lfloor>real x / real y\<rfloor>")
     apply auto
     apply (cases "y = 0")
      apply auto
     apply (cases "y = 1")
      apply auto
    apply (smt (verit, best) 1 add_implies_diff div_if divide_less_cancel
        floor_divide_of_nat_eq floor_eq4 floor_eq_iff floor_one le_numeral_extra(4)
        less_add_one nat_1 nat_le_real_less not_add_less2 not_gr0 of_nat_Suc
        of_nat_eq_0_iff of_nat_le_1_iff of_nat_less_0_iff)
    apply (cases "y = 0")
     apply auto
    apply (cases "y = 1")
     apply auto
    apply (drule 4)
    apply (drule 5)
    unfolding 6 apply simp
  proof -
    assume a1 [symmetric]: "\<lfloor>real x / real y\<rfloor> = \<lfloor>(real x - 1) / real y\<rfloor>" and
           a2: "0 < y" and
           a3: "y \<noteq> Suc 0" and
           a4: "real_of_int \<lfloor>(1 + real x) / real y\<rfloor> < (1 + real x) / real y" and
           a5: "real_of_int \<lfloor>(real x - 1) / real y\<rfloor> < real x / real y"
    have "\<lfloor>(1 + real x) / real y\<rfloor> \<ge> \<lfloor>real x / real y\<rfloor>"
      by (metis a2 divide_less_cancel floor_mono le_add_same_cancel2 linorder_not_less
          of_nat_0_less_iff zero_less_one_class.zero_le_one)
    moreover have "\<lfloor>(1 + real x) / real y\<rfloor> > \<lfloor>real x / real y\<rfloor> \<Longrightarrow> False"
    proof -
      assume a6: "\<lfloor>real x / real y\<rfloor> < \<lfloor>(1 + real x) / real y\<rfloor>"
      hence 1 [symmetric]: "\<lfloor>real x / real y\<rfloor> + 1 = \<lfloor>(1 + real x) / real y\<rfloor>"
        by (smt (verit, ccfv_SIG) One_nat_def Suc Suc_lessI a1 a3 a5 ceiling_eq
            divide_less_cancel floor_less_cancel nat_less_real_le of_nat_0_less_iff
            of_nat_less_1_iff real_of_int_floor_add_one_ge)
      have 2: "\<lfloor>real x / real y\<rfloor> + 1 = \<lceil>real x / real y\<rceil>" by (simp add: 6 Suc a1 a2)
      have 3: "real x / real y \<notin> \<int>" using a1 a5 by force
      have 4: "(1 + real x) / real y \<notin> \<int>" using a4 by auto
      have 5: "(real x - 1) / real y \<notin> \<int>" using a5
        by (smt (verit) 1 2 6 a1 a4 ceiling_of_nat div_by_1 divide_less_cancel floor_of_nat
            nat_le_real_less of_int_diff of_int_eq_1_iff of_int_floor of_nat_0_less_iff
            of_nat_1 of_nat_le_iff)
      note 6 = a4 [unfolded 1 2]
      have 7: "(1 + real x) / real y = real x / real y + 1 / real y" by argo
      have "\<lceil>real x / real y\<rceil> < \<lceil>(1 + real x) / real y\<rceil> \<Longrightarrow> False"
        apply (subst (asm) reals_ceiling_lt_iff)
          apply fact+
        unfolding 7 apply (frule reals_floors_lt_ex_exact)
        apply auto
      proof -
        fix z :: real
        assume a7: "\<lfloor>real x / real y\<rfloor> < \<lfloor>real x / real y + 1 / real y\<rfloor>" and
               a8: "z \<le> 1 / real y" and
               a9: "0 \<le> z" and
               a10: "real_of_int \<lfloor>real x / real y + 1 / real y\<rfloor> = real x / real y + z"
        have 8: "real x / real y + z \<in> \<int>" using a10 by (metis Ints_of_int)
        have 9: "z < 1" using a2 a3 a8
          by (smt (verit, ccfv_threshold) One_nat_def Suc_lessI divide_less_eq_1
              one_of_nat_less_iff)
        have 10: "z < 1 / real y"
          apply (rule ccontr)
          using a8 apply auto
          using 8 4 apply simp
          by argo
        have 11: "z > 0"
          apply (rule ccontr)
          using a9 apply auto
          using 8 3 by simp
        have 12: "(real x + z * real y) / real y \<in> \<int>" using 8
          by (simp add: add_divide_distrib)
        have 13: "\<And>x::real. x / real y \<in> \<int> \<Longrightarrow> x \<in> \<int>"
        proof -
          fix x :: real
          assume "x / real y \<in> \<int>"
          then obtain z :: int where "x / real y = z" by (rule Ints_cases)
          hence [symmetric]: "z * real y = x" using a2 by (simp add: nonzero_divide_eq_eq)
          thus "x \<in> \<int>" by simp
        qed
        have 14: "real x + z * real y \<in> \<int>" using 12 by (rule 13)
        have 15: "z * real y \<in> \<int>" apply (rule real_sum_in_Ints [THEN iffD1])
           apply fact
          by simp
        have 16: "z * real y > 0" by (simp add: 11 a2)
        have 17: "z * real y < 1"
          by (metis 10 11 16 div_by_1 nonzero_divide_mult_cancel_left not_less_iff_gr_or_eq
              pos_divide_less_eq zero_less_mult_iff)
        show False using 15 16 17 Ints_cases by force
      qed
      thus False using 3 4 a6 reals_ceiling_lt_iff by blast
    qed
    ultimately have 1: "\<lfloor>(1 + real x) / real y\<rfloor> = \<lfloor>real x / real y\<rfloor>" by fastforce
    show "\<lfloor>(1 + real x) / real y\<rfloor> + 1 = \<lfloor>(real x + real y) / real y\<rfloor>" unfolding 1
      by (metis One_nat_def a2 add_0 add_divide_distrib div_self less_add_one less_eq_Suc_le
          linorder_not_less one_add_floor one_of_nat_le_iff)
  qed
qed

lemma Uniq_E: "\<exists>\<^sub>\<le>\<^sub>1x. P x \<Longrightarrow> ((\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> x = y) \<Longrightarrow> Q) \<Longrightarrow> Q"
  unfolding Uniq_def by blast

lemma ex1I': "\<exists>x. P x \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1x. P x \<Longrightarrow> \<exists>!x. P x"
  by (simp add: ex1_iff_ex_Uniq)

lemma full_nat_induct2 [case_names 0 "lt_Suc"]:
  "P 0 \<Longrightarrow> (\<And>n. (\<And>m. m < Suc n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n)) \<Longrightarrow> P n"
  apply (induction n)
   apply auto
  by (metis gr0_conv_Suc infinite_descent0)

lemma full_nat_induct3 [case_names 0 "le_Suc"]:
  "P 0 \<Longrightarrow> (\<And>n. (\<And>m. m \<le> n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n)) \<Longrightarrow> P n"
  by (induction n rule: full_nat_induct2) simp_all

lemma full_nat_induct_at_least [consumes 1, case_names k "le_Suc"]:
  "k \<le> n \<Longrightarrow> P k \<Longrightarrow> (\<And>n. k \<le> n \<Longrightarrow> (\<And>m. k \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n)) \<Longrightarrow> P n"
  apply (induction n rule: full_nat_induct3)
   apply simp_all
  by (metis le_SucE)

lemma image_singleton_eq: "image f S = {y} \<Longrightarrow> x \<in> S \<Longrightarrow> f x = y"
  by auto

lemma image_singleton_eq': "image f S \<subseteq> {y} \<Longrightarrow> x \<in> S \<Longrightarrow> f x = y"
  by auto

lemma ifE: "P (if Q then X else Y) \<Longrightarrow> (Q \<Longrightarrow> P X \<Longrightarrow> R) \<Longrightarrow> (\<not>Q \<Longrightarrow> P Y \<Longrightarrow> R) \<Longrightarrow> R"
  by presburger

lemma inj_inj_implies_bij_exists: "inj (f :: 'a \<Rightarrow> 'b) \<Longrightarrow> inj (g :: 'b \<Rightarrow> 'a) \<Longrightarrow>
                                   \<exists>h :: 'a \<Rightarrow> 'b. bij h"
  by (metis (mono_tags, lifting) Schroeder_Bernstein top_greatest)

lemma nat_div_floor: "n div k = nat \<lfloor>n / k\<rfloor>"
  by (simp add: floor_divide_of_nat_eq)

lemma in_int_iff_eq_floor: "(x::real) \<in> \<int> \<longleftrightarrow> x = \<lfloor>x\<rfloor>"
  by auto (metis Ints_of_int)

lemma in_int_iff_eq_ceil: "(x::real) \<in> \<int> \<longleftrightarrow> x = \<lceil>x\<rceil>"
  by auto (metis Ints_of_int)

lemma in_nat_iff_dvd: "k > 0 \<Longrightarrow> (k::nat) dvd n \<longleftrightarrow> n / k \<in> \<nat>"
  apply auto
  apply (rule ccontr)
  unfolding dvd_def apply auto
proof -
  assume a1: "real n / real k \<in> \<nat>" and a2 [THEN spec]: "\<forall>l. n \<noteq> k * l" and a3: "0 < k"
  obtain q :: nat where q_def: "real q = real n / real k" using a1 by (metis a1 Nats_cases)
  have "real q * k = n" using q_def a3 by simp
  hence "q * k = n" by (metis of_nat_mult of_nat_eq_iff)
  thus False using a2 [of q] by auto
qed

lemma nats_div_floor_p1_ceil: "k > 0 \<Longrightarrow> \<not>(k::nat) dvd n \<Longrightarrow> \<lceil>n / k\<rceil> = \<lfloor>n / k\<rfloor> + 1"
  by (metis (no_types, lifting) Ints_of_int bot_nat_0.not_eq_extremum ceiling_altdef fraction_not_in_Ints
      of_int_of_nat_eq of_nat_0_eq_iff of_nat_dvd_iff)

lemma nat_mult_add_lt: "(i::nat) < k \<Longrightarrow> (j::nat) < l \<Longrightarrow> i * l + j < k * l"
  by (metis (mono_tags, lifting) Suc_le_eq add.commute add_0 add_diff_cancel_left' add_lessD1 diff_mult_distrib
      less_diff_conv n_less_m_mult_n nat_less_le nat_mult_1 order_less_trans plus_1_eq_Suc)

lemma natset_bounded_Max_bounded: "(S :: nat set) \<noteq> {} \<Longrightarrow> (\<And>n. n \<in> S \<Longrightarrow> n \<le> k) \<Longrightarrow> Max S \<le> k"
  by (meson Max_in finite_nat_set_iff_bounded_le)

lemma natset_has_minimum: "(S::nat set) \<noteq> {} \<Longrightarrow> \<exists>x\<in>S. \<forall>y\<in>S. x \<le> y"
proof -
  assume a1: "(S::nat set) \<noteq> {}"
    (* Proof from The Big Book of Real Analysis (Lemma 2.3.6) by Syafiq Johar *)
  have 1: "(n::nat) \<in> S' \<Longrightarrow> n \<le> k \<Longrightarrow> \<exists>x\<in>S'. \<forall>y\<in>S'. x \<le> y" for n k :: nat and S' :: "nat set"
  proof (induction k arbitrary: n)
    case 0
    then show ?case by blast
  next
    case (Suc k)
    then show ?case by (metis Suc.prems(2) Suc.prems(1) le_antisym not_less_eq_eq)
  qed
  obtain n :: nat where n_in_S: "n \<in> S" using a1 by blast
  show "\<exists>x\<in>S. \<forall>y\<in>S. x \<le> y" using 1 [OF n_in_S Nat.le_refl] .
qed

lemma natset_has_unique_minimum: "(S::nat set) \<noteq> {} \<Longrightarrow> \<exists>!x\<in>S. \<forall>y\<in>S. x \<le> y"
  apply (rule ex1I')
  using natset_has_minimum apply meson
  apply (rule Uniq_I)
  by (metis antisym)

lemma natset_minimum:
  fixes S :: "nat set"
  assumes "S \<noteq> {}"
  obtains n :: nat where "n \<in> S" and "\<And>m. m \<in> S \<Longrightarrow> n \<le> m"
  using natset_has_minimum [OF assms] by blast

lemma set_not_empty_not_singleton_exists: "S \<noteq> {} \<Longrightarrow> S \<noteq> {a} \<Longrightarrow> \<exists>x. x \<noteq> a \<and> x \<in> S"
  by fast

lemma card_1_iff: "card S = 1 \<longleftrightarrow> (\<exists>x. S = {x})"
  by (simp add: card_Suc_eq)

lemma card_2_iff: "card S = 2 \<longleftrightarrow> (\<exists>x y. x \<noteq> y \<and> S = {x, y})"
  by (auto simp add: numeral_2_eq_2 card_Suc_eq)

lemma injI': "(\<And>x y. x \<noteq> y \<Longrightarrow> f x \<noteq> f y) \<Longrightarrow> inj f"
  by (blast intro: injI)

lemma inj_onI': "(\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> f x \<noteq> f y) \<Longrightarrow> inj_on f S"
  by (blast intro: inj_onI)

lemma bij_exists_after_remove: "bij_betw f S1 S2 \<Longrightarrow> x \<in> S1 \<Longrightarrow> y \<in> S2 \<Longrightarrow>
                                \<exists>g. bij_betw g (S1 - {x}) (S2 - {y})"
proof (cases "finite S1")
  case True
  assume a1: "bij_betw f S1 S2" and a2: "x \<in> S1" and a3: "y \<in> S2"
  have 1: "card S1 = card S2" using a1 by (rule bij_betw_same_card)
  have 2: "finite S2" using True a1 bij_betw_finite by blast
  have 3: "Suc (card (S1 - {x})) = card S1" by (metis a2 card_Suc_Diff1 True)
  have 4: "Suc (card (S2 - {y})) = card S2" by (metis a3 card_Suc_Diff1 2)
  have 5: "card (S1 - {x}) = card (S2 - {y})" using 1 3 4 by linarith
  show ?thesis using 5 by (simp add: 2 True bij_betw_iff_card)
next
  case False
  assume a1: "bij_betw f S1 S2"
  have 1: "infinite S2" using a1 False bij_betw_finite by auto
  have 2: "\<exists>g. bij_betw g S1 (S1 - {x})" by (metis False infinite_imp_bij_betw)
  have 3: "\<exists>h. bij_betw h S2 (S2 - {y})" by (metis 1 infinite_imp_bij_betw)
  show ?thesis using 2 3 apply auto
    by (meson a1 bij_betw_the_inv_into bij_betw_trans)
qed

lemma bij_two_fixed:
  fixes x y :: 'a and S1 :: "'a set" and a b :: 'b and S2 :: "'b set" and f :: "'a \<Rightarrow> 'b"
  assumes "bij_betw f S1 S2" and "x \<in> S1" and "y \<in> S1" and "x \<noteq> y" and "a \<noteq> b" and "a \<in> S2" and "b \<in> S2"
  obtains f' :: "'a \<Rightarrow> 'b" where "bij_betw f' S1 S2" and "f' x = a" and "f' y = b"
proof -
  assume a1: "\<And>f'. bij_betw f' S1 S2 \<Longrightarrow> f' x = a \<Longrightarrow> f' y = b \<Longrightarrow> thesis"
  define g :: "'b \<Rightarrow> 'a" where "g \<equiv> inv_into S1 f"
  have 1: "bij_betw g S2 S1" using assms(1) unfolding g_def by (rule bij_betw_inv_into)
  have 2: "\<And>x. x \<in> S1 \<Longrightarrow> g (f x) = x" unfolding g_def using assms(1) by (simp add: bij_betw_def)
  have 3: "\<And>x. x \<in> S2 \<Longrightarrow> f (g x) = x" unfolding g_def using assms(1) by (simp add: bij_betw_def f_inv_into_f)
  obtain h :: "'a \<Rightarrow> 'b" where h_bij: "bij_betw h (S1 - {x}) (S2 - {a})"
    using assms bij_exists_after_remove by meson
  have y_in: "y \<in> S1 - {x}" using assms by blast
  have b_in: "b \<in> S2 - {a}" using assms by blast
  obtain h' :: "'a \<Rightarrow> 'b" where h'_bij: "bij_betw h' (S1 - {x} - {y}) (S2 - {a} - {b})"
    using y_in b_in h_bij bij_exists_after_remove by meson
  define f' :: "'a \<Rightarrow> 'b" where "\<And>z. f' z \<equiv> if z = x then a else if z = y then b else h' z"
  have 4: "inj_on f' S1"
    apply (rule inj_onI')
    unfolding f'_def apply auto
    using assms(4) apply blast
    using assms(5) apply blast
          apply (metis Diff_iff bij_betw_def h'_bij image_eqI insert_Diff_single insert_iff)
    using assms apply simp_all
    using h'_bij [unfolded bij_betw_def, THEN conjunct2] apply blast
    using h'_bij [unfolded bij_betw_def, THEN conjunct2] apply blast
    using h'_bij [unfolded bij_betw_def, THEN conjunct2] apply blast
    by (smt (verit, best) Diff_iff bij_betw_iff_bijections h'_bij singletonD)
  define h'_inv :: "'b \<Rightarrow> 'a" where "h'_inv \<equiv> inv_into (S1 - {x} - {y}) h'"
  have h'_inv_bij: "bij_betw h'_inv (S2 - {a} - {b}) (S1 - {x} - {y})"
    unfolding h'_inv_def using h'_bij by (rule bij_betw_inv_into)
  have h'_h'_inv: "\<And>z. z \<in> S2 - {a} - {b} \<Longrightarrow> h' (h'_inv z) = z"
    unfolding h'_inv_def using h'_bij by (rule bij_betw_inv_into_right)
  have h'_inv_h': "\<And>z. z \<in> S1 - {x} - {y} \<Longrightarrow> h'_inv (h' z) = z"
    unfolding h'_inv_def using h'_bij by (rule bij_betw_inv_into_left)
  have 5: "f' ` S1 = S2"
    unfolding image_def apply auto
    unfolding f'_def apply simp
     apply auto[1]
        apply (rule assms(6))
       apply (rule assms(7))
      apply (rule assms(6))
    using h'_bij [unfolded bij_betw_def, THEN conjunct2] apply fast
  proof -
    fix z :: 'b
    assume a1: "z \<in> S2"
    show "\<exists>z'\<in>S1. z = (if z' = x then a else if z' = y then b else h' z')"
    proof (cases "z = a")
      case True
      show ?thesis apply (rule bexI [where x=x])
         apply (simp add: True)
        by fact
    next
      case 1: False
      show ?thesis
      proof (cases "z = b")
        case True
        show ?thesis apply (rule bexI [where x=y])
          using assms(4) apply (simp add: True)
          by fact
      next
        case False
        have 2: "h'_inv z \<in> (S1 - {x} - {y})"
          using 1 False h'_inv_bij [unfolded bij_betw_def, THEN conjunct2] a1 by fast
        show ?thesis apply (rule bexI [where x="h'_inv z"])
           apply (subst h'_h'_inv)
          using a1 1 False apply blast
          using 2 apply simp
          using 2 by blast
      qed
    qed
  qed
  show thesis
  proof (rule a1)
    show "bij_betw f' S1 S2"
      unfolding bij_betw_def using 4 5 ..
    show "f' x = a" unfolding f'_def by simp
    show "f' y = b" unfolding f'_def using assms by simp
  qed
qed
end
