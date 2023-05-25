theory Digits
  imports Discrete_Log
    "HOL-Computational_Algebra.Polynomial"
begin

text\<open>Get digits of natural numbers in any base.\<close>

fun digits :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "digits base    0 = []"
| "digits 0       n = []"
| "digits (Suc 0) n = replicate n 1"
| "digits base    n = n mod base # digits base (n div base)"

lemma digits_induct[case_names 0 base0 base1 step]:
  assumes 0: "\<And>b. P b 0"
    and base0: "\<And>n. P 0 (Suc n)"
    and base1: "\<And>n. P (Suc 0) (Suc n)"
    and step: "\<And>b n. b > 1 \<Longrightarrow> n > 0 \<Longrightarrow> P b (n div b) \<Longrightarrow> P b n"
  shows "P b n"
  using step by (intro digits.induct[of P b n, OF 0 base0 base1]) simp


lemma digits_def:
  assumes "b > 1"
  shows "digits b n = (if n = 0 then [] else n mod b # digits b (n div b))"
proof -
  from \<open>b > 1\<close> obtain b' where "b = Suc (Suc b')" using less_iff_Suc_add by auto
  then show ?thesis by (induction n) auto
qed

lemma digits_simps[simp]:
  assumes "b > 1" and "n > 0"
  shows "digits b n = n mod b # digits b (n div b)"
  unfolding digits_def[of b n, OF \<open>b > 1\<close>] using \<open>n > 0\<close> by presburger

lemma digits_Nil_iff[iff]: "digits b n = [] \<longleftrightarrow> b = 0 \<or> n = 0"
  by (induction b n rule: digits.induct) auto

lemma single_digit[simp]:
  assumes "0 < n" and "n < b"
  shows "digits b n = [n]"
proof -
  from assms have "b > 1" by simp
  then show ?thesis using assms by force
qed

lemma digits_div: "b > 1 \<Longrightarrow> digits b (n div b) = tl (digits b n)"
  by (subst (2) digits_def) auto

lemma hd_digits: "b > 1 \<Longrightarrow> n > 0 \<Longrightarrow> hd (digits b n) = n mod b" by force

lemma length_digits_1[simp]: "digits (Suc 0) n = replicate n 1" by (induction n) auto

lemma length_digits:
  assumes "b > 1"
    and "n > 0"
  shows "length (digits b n) = nat_log b n + 1"
  using assms
proof (induction n rule: log_induct)
  case (less n)
  then have "length (digits b n) = 1" unfolding digits_def[OF \<open>b > 1\<close>, of n] by simp
  also from less have "... = nat_log b n + 1" by fastforce
  finally show ?case .
next
  from \<open>b > 1\<close> interpret nat_log_base by blast

  case (div n)
  from \<open>n \<ge> b\<close> and \<open>n > 0\<close> and \<open>b > 1\<close> have "n div b > 0" using div_eq_0_iff linorder_not_less by blast

  from \<open>n > 0\<close> have "length (digits b n) = length (digits b (n div b)) + 1"
    unfolding digits_def[OF \<open>b > 1\<close>, of n] by fastforce
  also from \<open>n div b > 0\<close> have "... = nat_log b (n div b) + 1 + 1" unfolding add_right_cancel by (fact div.IH)
  also have "... = nat_log b n + 1" unfolding add_right_cancel nat_log_def[OF \<open>n \<ge> b\<close>] by presburger
  finally show ?case .
qed


text\<open>Note: \<^const>\<open>poly\<close> evaluates a polynomial \<^term>\<open>p :: 'a poly\<close> at a given point \<^term>\<open>x :: 'a\<close>,
  \<^const>\<open>Poly\<close> constructs a polynomial \<^term>\<open>p :: 'a poly\<close> from a list of coefficients \<^term>\<open>cs :: 'a list\<close>.\<close>

definition from_digits :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "from_digits base ds = poly (Poly ds) base"


lemma from_digits_simps[simp]: "from_digits b (d # ds) = d + b * from_digits b ds"
  unfolding from_digits_def Poly.simps poly_pCons ..

lemma from_digits_altdef: "from_digits b ds = (\<Sum>i<length ds. ds ! i * b ^ i)"
proof (induction ds)
  case (Cons d ds)
  have "from_digits b (d # ds) = d + b * (\<Sum>i<length ds. ds ! i * b ^ i)"
    by (simp add: Cons.IH sum.lessThan_Suc_shift)
  also have "... = d + (\<Sum>i<length ds. ds ! i * (b ^ Suc i))"
    unfolding sum_distrib_left by (simp add: mult.left_commute)
  also have "... = (\<Sum>i<length (d # ds). (d # ds) ! i * b ^ i)"
    unfolding length_Cons sum.lessThan_Suc_shift by simp
  finally show ?case .
qed \<comment> \<open>case \<open>ds = []\<close> by\<close> (simp add: from_digits_def)


lemma from_digits_digits:
  assumes "b > 1"
  shows "from_digits b (digits b n) = n"
proof (induction "digits b n" arbitrary: n)
  case Nil
  then have "digits b n = []" ..
  with \<open>b > 1\<close> have "n = 0" by blast
  from \<open>b > 1\<close> show ?case unfolding \<open>n = 0\<close> from_digits_def by simp
next
  case (Cons d ds)
  note * = \<open>d # ds = digits b n\<close>[symmetric]
  from * have "digits b n \<noteq> []" by simp
  then have "n > 0" by blast

  from * have "ds = digits b (n div b)" unfolding digits_div[OF \<open>b > 1\<close>] by simp
  with Cons.hyps(1) have [simp]: "from_digits b (digits b (n div b)) = n div b" .

  from \<open>b > 1\<close> and \<open>n > 0\<close> show "from_digits b (digits b n) = n" by fastforce
qed


abbreviation nth_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nth_digit base n i \<equiv> nth_default 0 (digits base n) i"

lemma nth_digit:
  assumes "b > 1"
  shows "nth_default 0 (digits b n) i = (n div (b ^ i)) mod b"
proof (cases "n = 0")
  assume "n \<noteq> 0"
  then show ?thesis
  proof (induction i arbitrary: n)
    case 0
    with \<open>n \<noteq> 0\<close> show ?case unfolding digits_def[of b n, OF \<open>b > 1\<close>] by simp
  next
    case (Suc i)
    from \<open>b > 1\<close> and \<open>n \<noteq> 0\<close> have "digits b n = n mod b # digits b (n div b)" by force
    then have "nth_default 0 (digits b n) (Suc i) = nth_default 0 (digits b (n div b)) i" by force
    also have "... = n div b div b ^ i mod b"
    proof (cases "n div b > 0")
      case True  thus ?thesis using Suc.IH by blast next
      case False thus ?thesis by simp
    qed
    also have "... = n div b ^ Suc i mod b" unfolding power_Suc div_mult2_eq ..
    finally show ?case .
  qed
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp


end
