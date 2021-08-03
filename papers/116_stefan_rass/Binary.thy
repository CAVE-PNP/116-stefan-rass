theory Binary
  imports Main "Supplementary/Lists" "Supplementary/Discrete_Log" "HOL-Library.Sublist"
begin


section\<open>Binary String Representation\<close>

text\<open>In the paper "On the Existence of Weak One-Way Functions",
  a binary alphabet \<open>\<Sigma> := {0, 1}\<close> is used for virtually all TM related definitions.
  Therefore, a strong theory of binary strings is required for reasoning.

  There are two main influences for this theory:
  \<^theory>\<open>HOL.List\<close> (with datatype \<^typ>\<open>bool list\<close>) that caters to the string aspect,
  and \<^theory>\<open>HOL.Num\<close> (with \<^typ>\<open>num\<close>) which is implemented as a basis
  for efficient handling of numeric values in Isabelle.
  \<^typ>\<open>num\<close> is part of a big library and has useful properties
  (such as an almost injective mapping to integers) but ultimately lacks the flexibility
  required for effective string manipulation.
  We therefore chose the type of lists of boolean values (\<^typ>\<open>bool list\<close>),
  since it allows use to use the numerous lemmas proven for lists
  (see for instance in \<^theory>\<open>HOL.List\<close> or \<^theory>\<open>HOL-Library.Sublist\<close>)
  as well as the already set-up integration in automation tools.\<close>

type_synonym bin = "bool list"

text\<open>We follow the classical conventions of \<open>0 := False, 1 := True\<close>
  (we choose booleans for being a well-known two-valued type commonly associated with binary digits)
  and (unintuitively) let the most-significant-bit (MSB) be the \<^emph>\<open>last\<close> element of the list,
  to keep the following definitions from becoming overly complex.
  This results in representing strings mirrored compared to the common convention
  of having the MSB be the leftmost one.\<close>

fun nat_of_bin :: "bin \<Rightarrow> nat" ("'(_')\<^sub>2") where
  "nat_of_bin [] = 0" |
  "nat_of_bin (a # xs) = (if a then 1 else 0) + 2 * nat_of_bin xs"

fun inc :: "bin \<Rightarrow> bin" where
  "inc [] = [True]" |
  "inc (a # xs) = (if a then (False # inc xs) else (True # xs))"

fun bin_of_nat :: "nat \<Rightarrow> bin" where
  "bin_of_nat 0 = []" |
  "bin_of_nat (Suc n) = inc (bin_of_nat n)"

\<comment> \<open>For binary numbers, as stated in the paper (ch. 1, p. 2),
  the "least significant bit is located at the right end".
  The recursive definitions for binary strings result in somewhat unintuitive definitions:
  The number \<open>6\<^sub>1\<^sub>0\<close> is written \<open>110\<^sub>2\<close> in binary, but as \<^typ>\<open>bin\<close>,
  it is \<^term>\<open>[False, True, True]\<close> (an abbreviation for \<^term>\<open>False # True # True # []\<close>).
  This results in some strange properties including swapping prefix and suffix:
  the concepts of \<^const>\<open>prefix\<close> and \<^const>\<open>suffix\<close> defined over lists (see \<^theory>\<open>HOL-Library.Sublist\<close>)
  mean their exact opposites when applied to our definition of \<^typ>\<open>bin\<close>.\<close>

value "([False, True, True])\<^sub>2"


subsection\<open>Numeric Properties\<close>

lemma inc_not_Nil: "inc xs \<noteq> []" by (induction xs) auto
lemma inc_Suc: "Suc (nat_of_bin xs) = nat_of_bin (inc xs)" by (induction xs) auto
lemma inc_inc: "xs \<noteq> [] \<Longrightarrow> inc (inc (x # xs)) = x # (inc xs)" by force

lemma nat_of_bin_app0: "nat_of_bin (xs @ [False]) = nat_of_bin xs" by (induction xs) auto
lemma nat_of_bin_app1: "nat_of_bin (xs @ [True]) = nat_of_bin xs + 2 ^ length xs"
  by (induction xs) auto

lemma nat_of_bin_app: "nat_of_bin (lo @ up) = (nat_of_bin up) * 2^(length lo) + (nat_of_bin lo)"
  by (induction lo) auto

lemma nat_of_bin_0s [simp]: "nat_of_bin (replicate k False) = 0" by (induction k) auto
corollary nat_of_bin_app_0s: "nat_of_bin (replicate k False @ up) = (nat_of_bin up) * 2^k"
  using nat_of_bin_app by simp
corollary nat_of_bin_leading_0s[simp]: "nat_of_bin (xs @ replicate k False) = nat_of_bin xs"
  using nat_of_bin_app by simp

lemma hd_one_nonzero: "nat_of_bin (True # xs) > 0" by simp

lemma nat_of_bin_div2': "nat_of_bin xs div 2 = nat_of_bin (tl xs)" by (cases xs) auto
lemma nat_of_bin_div2[simp]: "nat_of_bin (a # xs) div 2 = nat_of_bin xs"
  unfolding nat_of_bin_div2' by simp

lemma nat_of_bin_max: "nat_of_bin xs < 2 ^ (length xs)" by (induction xs) auto
lemma nat_of_bin_min: "ends_in True xs \<Longrightarrow> nat_of_bin xs \<ge> 2 ^ (length xs - 1)"
  by (auto simp add: nat_of_bin_app1)


lemma bin_of_nat_double: "n > 0 \<Longrightarrow> bin_of_nat (2 * n) = False # (bin_of_nat n)"
proof (induction n rule: nat_induct_non_zero)
  case (Suc n)
  have "bin_of_nat (2 * Suc n) = inc (inc (bin_of_nat (2 * n)))" by simp
  also have "... = inc (inc (False # bin_of_nat n))" unfolding Suc.IH ..
  also have "... = False # inc (bin_of_nat n)" using inc_inc by simp
  also have "... = False # bin_of_nat (Suc n)" by simp
  finally show ?case .
qed (* case 1 by *) (simp add: numeral_2_eq_2)

corollary bin_of_nat_double_p1: "bin_of_nat (2 * n + 1) = True # (bin_of_nat n)"
  using bin_of_nat_double by (cases "n > 0") auto


corollary nat_of_bin_drop: "nat_of_bin (drop k xs) = (nat_of_bin xs) div 2 ^ k"
  (is "?n (drop k xs) = (?n xs) div 2 ^ k")
proof (induction k)
  case (Suc k)
  have "?n (drop (Suc k) xs) = ?n (tl (drop k xs))" unfolding drop_Suc drop_tl ..
  also have "... = ?n (drop k xs) div 2" unfolding nat_of_bin_div2' ..
  also have "... = ?n xs div 2 ^ k div 2" unfolding Suc.IH ..
  also have "... = ?n xs div (2 ^ k * 2)" unfolding div_mult2_eq ..
  also have "... = ?n xs div 2 ^ Suc k" unfolding power_Suc2 ..
  finally show ?case .
qed (* case "k = 0" by *) simp


subsection\<open>Addressing Leading Zeroes\<close>

text\<open>\<^typ>\<open>bin\<close> enables arbitrary string manipulation, but makes reasoning about
  numeric values more difficult, since leading zeroes cause non-injectivity.
  (\<^typ>\<open>num\<close> avoids this issue by defining the MSB to always be \<open>1\<close>,
  at the cost of being able to represent arbitrary strings.)
  To remedy this limitation when handling numeric values, we make use of \<^const>\<open>ends_in\<close>.\<close>

lemma inc_end_True[simp]:
  fixes xs
  assumes "ends_in True xs"
  shows "ends_in True (inc xs)"
  using assms
proof (induction xs)
  case (Cons a xs')
  from Cons.prems obtain ys where ysD: "a # xs' = ys @ [True]" ..
  then show ?case
  proof (cases ys)
    case Nil
    with ysD show ?thesis by simp
  next
    case (Cons b ys')
    with ysD have h1: "xs' = ys' @ [True]" by fastforce
    with Cons.IH obtain zs' where h2: "inc xs' = zs' @ [True]" by auto
    then show ?thesis by (cases a) (auto simp add: h1 h2)
  qed
qed (* case "xs = []" by *) simp

lemma bin_of_nat_gt_0_end_True[simp]: "n > 0 \<Longrightarrow> ends_in True (bin_of_nat n)"
proof (induction n rule: nat_induct_non_zero)
  case (Suc n)
  from \<open>ends_in True (bin_of_nat n)\<close> show ?case
    unfolding bin_of_nat.simps by (rule inc_end_True)
qed (* case "n = 1" by *) simp

lemma nat_of_bin_gt_0_end_True[simp]:
  assumes eTw: "ends_in True w"
  shows "nat_of_bin w > 0"
proof -
  have "(0::nat) < 2 ^ 0" by (rule less_exp)
  also have "... \<le> 2 ^ (length w - 1)" by fastforce
  also have "... \<le> nat_of_bin w" using nat_of_bin_min eTw .
  finally show ?thesis .
qed


subsection\<open>String Length\<close>

lemma inc_len: "length xs \<le> length (inc xs)"
  by (induction xs) auto

lemma nat_of_bin_len_mono:
  assumes e: "ends_in True ys"
    and l: "length xs < length ys"
  shows "nat_of_bin xs < nat_of_bin ys"
proof -
  have "nat_of_bin xs < 2 ^ (length xs)" by (rule nat_of_bin_max)
  also have "... \<le> 2 ^ (length ys - 1)" using l by fastforce
  also have "... \<le> nat_of_bin ys" using e by (rule nat_of_bin_min)
  finally show ?thesis .
qed


subsubsection\<open>Bit-Length\<close>

text\<open>The number of bits in the binary representation.
  This does not count any leading zeroes; the bit-length of \<open>0\<close> is \<open>0\<close>.\<close>

abbreviation (input) bit_length :: "nat \<Rightarrow> nat" where
  "bit_length n \<equiv> length (bin_of_nat n)"


lemma bit_length_mono: "mono bit_length"
proof (subst mono_iff_le_Suc, intro allI)
  fix n
  have "bit_length n \<le> length (inc (bin_of_nat n))" using inc_len .
  also have "... = bit_length (Suc n)" by simp
  finally show "bit_length n \<le> bit_length (Suc n)" .
qed

lemma bin_of_nat_len_gt_0[simp]: "n > 0 \<Longrightarrow> bit_length n > 0"
proof (induction n rule: nat_induct_non_zero)
  case (Suc n)
  have "0 < length (bin_of_nat n)" using Suc.IH .
  also have "... \<le> length (inc (bin_of_nat n))" by (rule inc_len)
  also have "... = length (bin_of_nat (Suc n))" by simp
  finally show ?case .
qed (* case "n = 1" by *) simp

lemma bit_len_eq_0_iff[iff]: "bit_length n = 0 \<longleftrightarrow> n = 0" using bin_of_nat_len_gt_0
proof (intro iffI)
  assume "bit_length n = 0"
  then have "\<not> bit_length n > 0" ..
  then have "\<not> n > 0" using bin_of_nat_len_gt_0 by (rule contrapos_nn)
  then show "n = 0" ..
qed (* direction "\<longleftarrow>" by *) simp

corollary bit_len_gt_0_iff[iff]: "bit_length n > 0 \<longleftrightarrow> n > 0" using bit_len_eq_0_iff by simp


corollary bit_len_double: "n > 0 \<Longrightarrow> bit_length (2 * n) = bit_length n + 1"
  unfolding bin_of_nat_double by simp

lemma bit_len_even_odd: "n > 0 \<Longrightarrow> bit_length (2 * n) = bit_length (2 * n + 1)"
proof -
  assume "n > 0"
  then have "bit_length (2 * n) = length (False # bin_of_nat n)" by (subst bin_of_nat_double) simp_all
  also have "... = length (True # bin_of_nat n)" by simp
  also have "... = bit_length (2 * n + 1)" unfolding bin_of_nat_double_p1 ..
  finally show ?thesis .
qed


subsection\<open>Inverses\<close>

lemma nat_bin_nat[simp]: "nat_of_bin (bin_of_nat (n)) = n" (is "?nbn n = n")
proof (induction n)
  case (Suc n)
  have "?nbn (Suc n) = nat_of_bin (inc (bin_of_nat n))" by simp
  also have "... = Suc (?nbn n)" using inc_Suc by simp
  also have "... = Suc n" using Suc.IH by simp
  finally show ?case .
qed (* case "n = 0" by *) simp

corollary surj_nat_of_bin: "surj nat_of_bin" using nat_bin_nat by (intro surjI)

lemma bin_nat_bin[simp]: "ends_in True w \<Longrightarrow> bin_of_nat (nat_of_bin w) = w"
proof (induction w)
  let ?b = bin_of_nat and ?n = nat_of_bin
  case (Cons a w)
  note IH = Cons.IH and prems1 = Cons.prems
  show ?case
  proof (cases w)
    case Nil
    with \<open>ends_in True (a # w)\<close> have "a" (* == True *) by simp
    with \<open>w = []\<close> show ?thesis by simp
  next
    case (Cons a' w')
    with prems1 have "ends_in True w" by (intro ends_in_Cons) blast+
    with nat_of_bin_gt_0_end_True have "?n w > 0" .
    show ?thesis
    proof (cases a)
      case True
      then have "?b (?n (a # w)) = inc (?b (2 * ?n w))" by simp
      also have "... = inc (False # ?b (?n w))" using bin_of_nat_double \<open>?n w > 0\<close> by auto
      also have "... = inc (False # w)" using IH \<open>ends_in True w\<close> by presburger
      also have "... = a # w" using \<open>a\<close> by simp
      finally show ?thesis .
    next
      case False
      then have "?b (?n (a # w)) = ?b (2 * ?n w)" by simp
      also have "... = False # ?b (?n w)" using bin_of_nat_double \<open>?n w > 0\<close> by auto
      also have "... = False # w" using IH \<open>ends_in True w\<close> by presburger
      also have "... = a # w" using \<open>\<not>a\<close> by simp
      finally show ?thesis .
    qed
  qed
qed (* case "w = []" by *) simp

corollary inj_on_nat_of_bin: "inj_on nat_of_bin {w. ends_in True w}"
  by (intro inj_on_inverseI, elim CollectE) (rule bin_nat_bin)

lemma bij_nat_of_bin: "bij_betw nat_of_bin {w. ends_in True w} {0<..}" using inj_on_nat_of_bin
proof (intro bij_betw_imageI)
  show "nat_of_bin ` {w. ends_in True w} = {0<..}"
  proof safe (* intro subset_antisym subsetI, unfold greaterThan_iff, elim imageE forw_subst CollectE exE *)
    fix w
    show "nat_of_bin (w @ [True]) > 0" by (intro nat_of_bin_gt_0_end_True) blast
  next
    fix n::nat assume "n > 0"
    show "n \<in> nat_of_bin ` {w. ends_in True w}"
    proof (intro image_eqI[where x="bin_of_nat n"] CollectI)
      show "n = nat_of_bin (bin_of_nat n)" by simp
      show "ends_in True (bin_of_nat n)" using \<open>n > 0\<close> by (rule bin_of_nat_gt_0_end_True)
    qed
  qed
qed


subsection\<open>Advanced Properties\<close>

lemma bin_of_nat_div2: "bin_of_nat (n div 2) = tl (bin_of_nat n)"
proof (cases "n > 1")
  case False
  then have "n = 0 \<or> n = 1" by fastforce
  then show ?thesis by (elim disjE) auto
next
  case True
  define w where "w \<equiv> bin_of_nat n"
  have "nat_of_bin w = nat_of_bin (bin_of_nat n)" unfolding w_def ..
  then have wI: "nat_of_bin w = n" by simp

  from \<open>n > 1\<close> have "n \<ge> 2" by simp
  have "1 < length (bin_of_nat 2)" unfolding numeral_2_eq_2 by simp
  also have "... \<le> length w" unfolding w_def using bit_length_mono \<open>n \<ge> 2\<close> ..
  finally have "length w > 1" .

  with less_trans zero_less_one have "w \<noteq> []" by (fold length_greater_0_conv)
  with hd_Cons_tl have w_split: "hd w # tl w = w" .

  have eTw: "ends_in True w" unfolding w_def using bin_of_nat_gt_0_end_True \<open>n > 1\<close> by simp
  then have "ends_in True (hd w # tl w)" unfolding w_split .

  from \<open>length w > 1\<close> have "length (tl w) > 0" unfolding length_tl less_diff_conv add_0 .
  then have "tl w \<noteq> []" unfolding length_greater_0_conv .
  with ends_in_Cons[of "hd w" "tl w"] eTw have eTtw: "ends_in True (tl w)" unfolding w_split .

  have "bin_of_nat (n div 2) = bin_of_nat (nat_of_bin w div 2)" unfolding wI ..
  also have "... = bin_of_nat (nat_of_bin (tl w))" using nat_of_bin_div2' by simp
  also have "... = tl w" using bin_nat_bin eTtw .
  finally show ?thesis unfolding w_def .
qed

corollary bin_of_nat_div2_times2: "n > 1 \<Longrightarrow> bin_of_nat (2 * (n div 2)) = False # tl (bin_of_nat n)"
  using bin_of_nat_div2 bin_of_nat_double by simp

corollary bin_of_nat_div2_times2_len: "n > 1 \<Longrightarrow> bit_length (2 * (n div 2)) = bit_length n"
proof -
  assume "n > 1"
  then have l: "bin_of_nat n \<noteq> []" using bin_of_nat_len_gt_0 by simp

  have "length (bin_of_nat (2 * (n div 2))) = length (False # tl (bin_of_nat n))"
    using bin_of_nat_div2_times2 \<open>n > 1\<close> by presburger
  also have "... = length (bin_of_nat n)" using len_tl_Cons l .
  finally show ?thesis .
qed

lemma bin_of_nat_app_0s:
  assumes "n > 0"
  shows "bin_of_nat (n * 2^k) = replicate k False @ bin_of_nat n"
    (is "?lhs = ?zs @ ?n")
proof -
  from \<open>n > 0\<close> have "?n \<noteq> []" using bin_of_nat_len_gt_0 by simp
  moreover from \<open>n > 0\<close> have "ends_in True ?n" by (rule bin_of_nat_gt_0_end_True)
  ultimately have eTr: "ends_in True (?zs @ ?n)" unfolding ends_in_append by simp

  have "?lhs = bin_of_nat (nat_of_bin ?n * 2^k)" by simp
  also have "... = bin_of_nat (nat_of_bin (?zs @ ?n))" using nat_of_bin_app_0s by simp
  also have "... = ?zs @ ?n" using eTr by simp
  finally show ?thesis .
qed

lemma nat_of_bin_app_1s: "nat_of_bin (replicate n True @ xs) = nat_of_bin xs * 2^n + 2^n - 1"
proof (induction n)
  case (Suc n)

  have h1: "c \<ge> a \<Longrightarrow> a \<ge> b \<Longrightarrow> c - a + b = c - (a - b)" for a b c ::nat by simp
  have h2: "nat_of_bin xs * 2^(Suc n) + 2^(Suc n) \<ge> 2" by (intro trans_le_add2) simp
  note h3 = h2[THEN h1]

  have "nat_of_bin (replicate (Suc n) True @ xs) = nat_of_bin (True # replicate n True @ xs)" by simp
  also have "\<dots> = 2 * (nat_of_bin xs * 2^n + 2^n - 1) + 1" using Suc.IH by simp
  also have "\<dots> = 2 * (nat_of_bin xs * 2^n + 2^n) - 2 + 1" unfolding diff_mult_distrib2 by simp
  also have "\<dots> = nat_of_bin xs * 2 * 2^n + 2 * 2^n - 2 + 1"
    unfolding add_mult_distrib2 mult.assoc[symmetric] by (subst mult.commute) rule
  also have "\<dots> = nat_of_bin xs * 2^(Suc n) + 2^(Suc n) - 2 + 1" unfolding power_Suc mult.assoc ..
  also have "\<dots> = nat_of_bin xs * 2^(Suc n) + 2^(Suc n) - 1" by (subst h3) simp_all
  finally show ?case .
qed (* case "n = 0" by *) simp

lemma bin_of_nat_end_True[iff]: "ends_in True (bin_of_nat n) \<longleftrightarrow> n > 0" (is "?lhs \<longleftrightarrow> ?rhs")
proof (intro iffI)
  show "?lhs \<Longrightarrow> ?rhs" by (drule nat_of_bin_gt_0_end_True) (unfold nat_bin_nat)
  show "?rhs \<Longrightarrow> ?lhs" by (rule bin_of_nat_gt_0_end_True)
qed


subsection\<open>Log and Bit-Length\<close>

lemma bit_len_eq_dlog:
  "n > 0 \<Longrightarrow> bit_length n = dlog n + 1" (is "n > 0 \<Longrightarrow> ?len n = ?log n + 1")
proof (induction n rule: log_induct)
  case (double n)
  have "bit_length n = bit_length (2 * (n div 2))" using \<open>n \<ge> 2\<close>
    by (subst bin_of_nat_div2_times2_len) force+
  also have "... = bit_length (n div 2) + 1" using \<open>n \<ge> 2\<close> by (subst bit_len_double) force+
  also have "... = dlog (n div 2) + 1 + 1" unfolding double.IH ..
  also have "... = dlog (n) + 1" using log_rec[of n] and \<open>n \<ge> 2\<close> by presburger
  finally show "bit_length n = dlog n + 1" .
qed (* case "n = 1" by *) force

lemma bit_length_eq_log:
  assumes "n > 0"
  shows "bit_length n = \<lfloor>log 2 n\<rfloor> + 1"
  using assms log_altdef bit_len_eq_dlog by auto


end
