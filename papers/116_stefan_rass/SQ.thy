theory SQ
  imports Complex_Main gn dens "HOL-Library.Discrete"
begin

subsection\<open>Language of integer squares\<close>

(* SQ is an overloaded identifier in the paper *)
definition SQ :: lang where \<comment> \<open>then language of non-zero square numbers, represented by binary string without leading ones\<close>
  "SQ \<equiv> {w. \<exists>x. gn w = x ^ 2}"

definition SQ_nat :: "nat set" where \<comment> \<open>the analogous set \<open>SQ \<subseteq> \<nat>\<close>, as defined in ch 4.1\<close>
  "(SQ_nat::nat set) \<equiv> {y. y \<noteq> 0 \<and> (\<exists>x. y = x ^ 2)}"

declare SQ_def[simp] SQ_nat_def[simp]

lemma SQ_nat_zero: 
	"insert 0 SQ_nat = {y. \<exists>x. y = x ^ 2}"
	"SQ_nat = {y. \<exists>x. y = x ^ 2} - {0}"
	by auto

(* relating SQ and SQ_nat *)
lemma SQ_SQ_nat:
  shows SQ_nat_vim: "SQ = nat_of_num -` SQ_nat"
    and SQ_nat_eq: "SQ = {w. nat_of_num w \<in> SQ_nat}"
  by (simp_all add: nat_of_num_pos)

lemma SQ_nat_im: "SQ_nat = gn ` SQ"
proof (standard; standard)
  fix n
  assume assm: "n \<in> SQ_nat"
  then have "n > 0" by simp
  from assm obtain x where b: "n = x ^ 2" by force
  with \<open>n > 0\<close> have "gn (gn_inv n) = x ^ 2" using inv_gn_id by (metis is_gn_def)
  then show "n \<in> gn ` SQ" using b by force
next
  fix n
  assume "n \<in> gn ` SQ"
  then have "n > 0" using gn_gt_0 by auto
  from \<open>n \<in> gn ` SQ\<close> have "n \<in> {n. \<exists>x. gn (gn_inv n) = x ^ 2}" using gn_inv_id by fastforce
  then have "\<exists>x. gn (gn_inv n) = x ^ 2" by blast
  then obtain x where "gn (gn_inv n) = x ^ 2" ..
  with \<open>n > 0\<close> have "n = x ^ 2" using inv_gn_id by simp
  with \<open>n > 0\<close> show "n \<in> SQ_nat" by simp
qed


lemma lemma_4_2: "dens SQ x = Discrete.sqrt x"
proof -
  have eq: "{w\<in>SQ. gn w \<le> x} = gn_inv ` power2 ` {0<..Discrete.sqrt x}"
  proof -
    have "{w\<in>SQ. gn w \<le> x} = {w. \<exists>z. (gn w = z^2 \<and> gn w \<le> x)}"
      using SQ_def by (smt (verit, best) Collect_cong mem_Collect_eq)
    also have "\<dots> = {w. \<exists>z. (gn w = z^2 \<and> z^2 \<le> x)}" by metis
    also have "\<dots> = {w. \<exists>z. (gn w = z^2 \<and> 0 < z^2 \<and> z^2 \<le> x)}"
      using gn_def nat_of_num_pos by metis
    also have "\<dots> = {gn_inv (z\<^sup>2) |z. 0 < z\<^sup>2 \<and> z\<^sup>2 \<le> x}"
      using gn_def gn_inv_def
      by (metis (mono_tags, hide_lams) gn_inv_id inv_gn_id is_gn_def)
    also have "\<dots> = {gn_inv (z\<^sup>2) |z. 0 < z \<and> z \<le> Discrete.sqrt x}"
      using le_sqrt_iff by force
    also have "\<dots> = gn_inv ` power2 ` {0<..Discrete.sqrt x}" by auto
    finally show ?thesis .
  qed
  then have "inj_on gn_inv (power2 ` {0<..Discrete.sqrt x})"
    by (smt (verit, best) gn_inv_def greaterThanAtMost_iff imageE inj_on_def nat_zero_less_power_iff num_of_nat_inverse)
  then have "dens SQ x = card (power2 ` {0<..Discrete.sqrt x})"
    using eq card_image by auto
  also have "\<dots> = card {0<..Discrete.sqrt x}"
    by (simp add: card_image inj_on_def)
  also have "\<dots> = Discrete.sqrt x" by simp
  finally show ?thesis .
qed


subsection\<open>Next integer square\<close>

definition next_square :: "nat \<Rightarrow> nat" where
  "next_square n = (Discrete.sqrt (n - 1) + 1)\<^sup>2"

declare next_square_def[simp]

abbreviation is_square :: "nat \<Rightarrow> bool" where
  "is_square n \<equiv> (\<exists>m. n = m\<^sup>2)"

corollary next_sq_correct1: "is_square (next_square n)" by simp

lemma next_sq_eq: "n > 0 \<Longrightarrow> is_square n \<Longrightarrow> next_square n = n"
proof -
  assume "n > 0" and "is_square n"
  with sqrt_Suc[of "n - 1"] have *: "Discrete.sqrt n = Discrete.sqrt (n - 1) + 1" by fastforce

  from \<open>is_square n\<close> have "n = (Discrete.sqrt n)\<^sup>2" by fastforce
  then have "n = (Discrete.sqrt (n - 1) + 1)\<^sup>2" by (unfold *)
  then show ?thesis by simp
qed

lemma next_sq_gt: "n > 0 \<Longrightarrow> \<not> is_square n \<Longrightarrow> next_square n > n"
proof -
  assume "n > 0" and "\<not> is_square n"
  with sqrt_Suc[of "n - 1"] have *: "Discrete.sqrt n = Discrete.sqrt (n - 1)" by force

  from Suc_sqrt_power2_gt have "n < (Discrete.sqrt n + 1)\<^sup>2" by simp
  then have "n < (Discrete.sqrt (n - 1) + 1)\<^sup>2" by (unfold *)
  then show ?thesis by simp
qed

lemma next_sq_correct2: "n \<le> next_square n"
proof (cases "n > 0")
  case False thus ?thesis by simp
next
  case True then show ?thesis
  proof (cases "is_square n")
    case True
    with next_sq_eq[of n] and \<open>n > 0\<close> show ?thesis using eq_imp_le by presburger 
  next
    case False
    with next_sq_gt[of n] and \<open>n > 0\<close> show ?thesis using less_imp_le_nat by blast
  qed
qed


corollary prev_sq_le_next_sq: "(Discrete.sqrt n)\<^sup>2 \<le> next_square n"
  using le_trans and sqrt_power2_le and next_sq_correct2 .

lemma next_sq_le_greater_sq: "next_square n \<le> (Discrete.sqrt n + 1)\<^sup>2"
  unfolding next_square_def using mono_sqrt' and power_mono by simp

lemma adj_sq_real: "(x + 1)\<^sup>2 - x\<^sup>2 = 2 * x + 1" for x :: real by algebra
lemma adj_sq_nat: "(x + 1)\<^sup>2 - x\<^sup>2 = 2 * x + 1" for x :: nat unfolding power2_eq_square mult_2 by simp


lemma bounded_diff: \<comment> \<open>difference of two bounded values is at most the difference of the bounds\<close>
  fixes a b l u :: nat
  shows "\<lbrakk>l \<le> a; a \<le> u; l \<le> b; b \<le> u\<rbrakk> \<Longrightarrow> b - a \<le> u - l"
  by auto

lemma next_sq_diff: "next_square n - n \<le> 2 * (Discrete.sqrt n) + 1"
proof -
  let ?s = "Discrete.sqrt n"
  let ?l = "?s\<^sup>2"
  and ?u = "(?s + 1)\<^sup>2"
  and ?a = n
  and ?b = "next_square n"

  note bounded_diff
  moreover have "?l \<le> ?a" using sqrt_power2_le .
  moreover have "?a \<le> ?u" using less_imp_le_nat[OF Suc_sqrt_power2_gt] by simp
  moreover have "?l \<le> ?b" using prev_sq_le_next_sq .
  moreover have "?b \<le> ?u" using next_sq_le_greater_sq .
  ultimately have "?b - ?a \<le> ?u - ?l" .
  then show "?b - ?a \<le> 2 * ?s + 1" unfolding adj_sq_nat .
qed

end
