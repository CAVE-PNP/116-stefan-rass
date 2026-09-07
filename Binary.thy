chapter\<open>Definitions and Preliminaries\<close>

section\<open>Binary String Representation\<close>

theory Binary
  imports Main "Supplementary/Lists" "Supplementary/Discrete_Log" "HOL-Library.Sublist"
    "Supplementary/Discrete_Sqrt"
begin


text\<open>In @{cite rassOwf2017},
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

text\<open>For binary numbers, as stated in @{cite \<open>ch.~1\<close> rassOwf2017},
  the "least significant bit is located at the right end".
  The recursive definitions for binary strings result in somewhat less intuitive definitions:
  The number \<open>6\<^sub>1\<^sub>0\<close> is written \<open>110\<^sub>2\<close> in binary, but as \<^typ>\<open>bin\<close>,
  it is \<^term>\<open>[False, True, True]\<close> (an abbreviation for \<open>False # True # True # []\<close>).
  This results in some strange properties including swapping prefix and suffix:
  the concepts of \<^const>\<open>prefix\<close> and \<^const>\<open>suffix\<close> defined over lists (see \<^theory>\<open>HOL-Library.Sublist\<close>)
  mean their exact opposites when applied to our definition of \<^typ>\<open>bin\<close>.\<close>

value "([False, True, True])\<^sub>2" \<comment> \<open>returns @{value "([False, True, True])\<^sub>2"}\<close>

subsection\<open>Numeric Properties\<close>

lemma length_inc_Suc_iff: "length (inc xs) = Suc (length xs) \<longleftrightarrow>
                           (\<exists>n. xs = replicate n True)"
  apply (induction xs)
   apply auto
     apply (metis replicate_Suc)
  by (simp_all add: Cons_replicate_eq)

lemma length_inc_eq_iff: "length (inc xs) = length xs \<longleftrightarrow> False \<in> set xs"
  by (induction xs) simp_all

lemma length_inc_cases [case_names eq plus1]: "(length (inc xs) = length xs \<Longrightarrow> P) \<Longrightarrow>
    (length (inc xs) = Suc (length xs) \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induction xs)
   apply auto
  by (metis (full_types) length_Cons)

lemma length_inc_rev [simp]: "length (inc (rev xs)) = length (inc xs)"
  apply (cases rule: length_inc_cases [of xs])
  unfolding length_inc_eq_iff length_inc_Suc_iff apply auto
  by (metis length_inc_eq_iff length_rev set_rev)

lemma inc_append_no_overflow: "False \<in> set b1 \<Longrightarrow> inc (b1 @ b2) = (inc b1) @ b2"
  by (induction b1) simp_all

lemma inc_append_overflow: "b1 = replicate n True \<Longrightarrow>
                            inc (b1 @ b2) = (replicate n False) @ inc b2"
  by (induction n arbitrary: b1) simp_all

lemma nat_of_bin_trim [simp]: "nat_of_bin (trimRight False b) = nat_of_bin b"
  apply (induction b)
   apply auto
   apply (smt (verit, ccfv_SIG) append.right_neutral append_Cons dropWhile.simps(2)
      dropWhile_append dropWhile_eq_Nil_conv nat_of_bin.simps(2) plus_1_eq_Suc
      rev.simps(1) rev_append rev_singleton_conv)
  by (smt (verit, ccfv_threshold) add_0 append_Cons append_Nil dropWhile.simps(1)
      dropWhile.simps(2) dropWhile_append dropWhile_eq_Nil_conv list.discI
      list.sel(2) list.sel(3) list.size(3) mult.assoc mult.commute mult.left_commute
      mult_0_right mult_2 mult_2_right nat_mult_1_right nat_of_bin.elims
      nat_of_bin.simps(1) nat_of_bin.simps(2) numerals(1) plus_1_eq_Suc
      remdups_adj.simps(2) remdups_adj_Cons' rev.simps(1) rev.simps(2) rev_append
      rev_eq_Cons_iff rev_rev_ident trim_def trim_left trim_nil)

lemma nat_of_bin_all_True [simp]: "nat_of_bin (replicate n True) = 2 ^ n - 1"
  apply (induction n)
   apply auto
  by (metis Suc_mask_eq_exp add_2_eq_Suc diff_Suc_Suc minus_nat.diff_0 mult_Suc_right)

lemma inc_not_Nil: "inc xs \<noteq> []" by (induction xs) auto
lemma inc_Suc: "Suc (nat_of_bin xs) = nat_of_bin (inc xs)" by (induction xs) auto
lemma inc_inc: "xs \<noteq> [] \<Longrightarrow> inc (inc (x # xs)) = x # (inc xs)" by force

lemma nat_of_bin_app0: "nat_of_bin (xs @ [False]) = nat_of_bin xs" by (induction xs) auto
lemma nat_of_bin_app1: "nat_of_bin (xs @ [True]) = nat_of_bin xs + 2 ^ length xs"
  by (induction xs) auto

lemma nat_of_bin_app: "nat_of_bin (lo @ up) = (nat_of_bin up) * 2^(length lo) + (nat_of_bin lo)"
  by (induction lo) auto

lemma nat_of_bin_0s [simp]: "nat_of_bin (False \<up> k) = 0" by (induction k) auto
corollary nat_of_bin_app_0s: "nat_of_bin (False \<up> k @ up) = (nat_of_bin up) * 2^k"
  using nat_of_bin_app by simp
corollary nat_of_bin_leading_0s[simp]: "nat_of_bin (xs @ False \<up> k) = nat_of_bin xs"
  using nat_of_bin_app by simp

lemma hd_one_nonzero: "nat_of_bin (True # xs) > 0" by simp

lemma nat_of_bin_trimRight [simp]: "(xs1@trimRight False xs2)\<^sub>2 = (xs1@xs2)\<^sub>2"
  apply (induction xs2)
   apply auto
  by (metis nat_of_bin_app nat_of_bin_trim rev.simps(2))

lemma nat_of_bin_div2': "nat_of_bin xs div 2 = nat_of_bin (tl xs)" by (cases xs) auto
lemma nat_of_bin_div2[simp]: "nat_of_bin (a # xs) div 2 = nat_of_bin xs"
  unfolding nat_of_bin_div2' by simp

lemma nat_of_bin_max: "nat_of_bin xs < 2 ^ (length xs)" by (induction xs) auto
lemma nat_of_bin_min: "ends_in True xs \<Longrightarrow> nat_of_bin xs \<ge> 2 ^ (length xs - 1)"
  by (auto simp: nat_of_bin_app1)


lemma bin_of_nat_double: "n > 0 \<Longrightarrow> bin_of_nat (2 * n) = False # (bin_of_nat n)"
  by (induction n rule: nat_induct_non_zero) (auto simp: numeral_2_eq_2 inc_inc)

corollary bin_of_nat_double_p1: "bin_of_nat (2 * n + 1) = True # (bin_of_nat n)"
  using bin_of_nat_double by (cases "n > 0") auto

corollary nat_of_bin_drop: "nat_of_bin (drop k xs) = (nat_of_bin xs) div 2 ^ k"
  (is "?n (drop k xs) = (?n xs) div 2 ^ k")
proof (induction k)
  case (Suc k)
  have "?n (drop (Suc k) xs) = ?n (tl (drop k xs))" unfolding drop_Suc drop_tl ..
  also have "... = ?n (drop k xs) div 2" unfolding nat_of_bin_div2' ..
  also have "... = ?n xs div 2 ^ k div 2" unfolding Suc.IH ..
  also have "... = ?n xs div 2 ^ Suc k" unfolding div_mult2_eq power_Suc2 ..
  finally show ?case .
qed \<comment> \<open>case \<^term>\<open>k = 0\<close> by\<close> simp

lemma nat_of_bin_eq_0_iff: "nat_of_bin xs = 0 \<longleftrightarrow> set xs \<subseteq> {False}"
proof
  assume a1: "(xs)\<^sub>2 = 0"
  then obtain n :: nat where xs_def: "xs = replicate n False"
    apply (induction xs)
     apply auto
    using trim_nil_eq by fastforce
  show "set xs \<subseteq> {False}" unfolding xs_def by auto
next
  assume "set xs \<subseteq> {False}"
  thus "(xs)\<^sub>2 = 0" by (metis nat_of_bin_0s replicate_set_eq)
qed

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
qed \<comment> \<open>case \<^term>\<open>xs = []\<close> by\<close> simp

lemma bin_of_nat_gt_0_end_True[simp]: "n > 0 \<Longrightarrow> ends_in True (bin_of_nat n)"
proof (induction n rule: nat_induct_non_zero)
  case (Suc n)
  from \<open>ends_in True (bin_of_nat n)\<close> show ?case
    unfolding bin_of_nat.simps by (rule inc_end_True)
qed \<comment> \<open>case \<^term>\<open>n = 1\<close> by\<close> simp

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

value "bit_length 0" \<comment> \<open>is @{value "bit_length 0"}\<close>


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
qed \<comment> \<open>case \<^term>\<open>n = 1\<close> by\<close> simp

lemma bit_len_eq_0_iff[iff]: "bit_length n = 0 \<longleftrightarrow> n = 0" using bin_of_nat_len_gt_0
proof (intro iffI)
  assume "bit_length n = 0"
  then have "\<not> bit_length n > 0" ..
  then have "\<not> n > 0" using bin_of_nat_len_gt_0 by (rule contrapos_nn)
  then show "n = 0" ..
qed \<comment> \<open>direction \<open>\<longleftarrow>\<close> by\<close> simp

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

lemma nat_bin_nat[simp]: "nat_of_bin (bin_of_nat n) = n" (is "?nbn n = n")
proof (induction n)
  case (Suc n)
  have "?nbn (Suc n) = nat_of_bin (inc (bin_of_nat n))" by simp
  also have "... = Suc (?nbn n)" using inc_Suc by simp
  also have "... = Suc n" using Suc.IH by simp
  finally show ?case .
qed \<comment> \<open>case \<^term>\<open>n = 0\<close> by\<close> simp

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
qed \<comment> \<open>case \<^term>\<open>w = []\<close> by\<close> simp

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

lemma bin_nat_bin_drop_zs: "bin_of_nat (nat_of_bin w) = rev (dropWhile (\<lambda>b. b = False) (rev w))"
proof (induction w rule: rev_induct)
  case (snoc x xs) thus ?case
  proof (induction x)
    case True  thus ?case by (subst bin_nat_bin) fastforce+
  next
    case False thus ?case unfolding nat_of_bin_app0 by force
  qed
qed \<comment> \<open>case \<^term>\<open>w = []\<close> by\<close> simp

lemma len_bin_nat_bin: "length (bin_of_nat (nat_of_bin w)) \<le> length w"
proof -
  have "bit_length (nat_of_bin w) = length (dropWhile (\<lambda>b. b = False) (rev w))" unfolding bin_nat_bin_drop_zs by force
  also have "... \<le> length (rev w)" by (rule length_dropWhile_le)
  finally show "bit_length (w)\<^sub>2 \<le> length w" unfolding length_rev .
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
  shows "bin_of_nat (n * 2^k) = False \<up> k @ bin_of_nat n"
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

lemma nat_of_bin_app_1s: "nat_of_bin (True \<up> n @ xs) = nat_of_bin xs * 2^n + 2^n - 1"
proof (induction n)
  case (Suc n)

  have h1: "c \<ge> a \<Longrightarrow> a \<ge> b \<Longrightarrow> c - a + b = c - (a - b)" for a b c ::nat by simp
  have h2: "nat_of_bin xs * 2^(Suc n) + 2^(Suc n) \<ge> 2" by (intro trans_le_add2) simp
  note h3 = h2[THEN h1]

  have "nat_of_bin (True \<up> (Suc n) @ xs) = nat_of_bin (True # True \<up> n  @ xs)" by simp
  also have "\<dots> = 2 * (nat_of_bin xs * 2^n + 2^n - 1) + 1" using Suc.IH by simp
  also have "\<dots> = 2 * (nat_of_bin xs * 2^n + 2^n) - 2 + 1" unfolding diff_mult_distrib2 by simp
  also have "\<dots> = nat_of_bin xs * 2 * 2^n + 2 * 2^n - 2 + 1"
    unfolding add_mult_distrib2 mult.assoc[symmetric] by (simp add: mult.commute)
  also have "\<dots> = nat_of_bin xs * 2^(Suc n) + 2^(Suc n) - 2 + 1" unfolding power_Suc mult.assoc ..
  also have "\<dots> = nat_of_bin xs * 2^(Suc n) + 2^(Suc n) - 1" by (subst h3) simp_all
  finally show ?case .
qed \<comment> \<open>case \<^term>\<open>n = 0\<close> by\<close> simp

lemma bin_of_nat_end_True[iff]: "ends_in True (bin_of_nat n) \<longleftrightarrow> n > 0" (is "?lhs \<longleftrightarrow> ?rhs")
proof (intro iffI)
  show "?lhs \<Longrightarrow> ?rhs" by (drule nat_of_bin_gt_0_end_True) (unfold nat_bin_nat)
  show "?rhs \<Longrightarrow> ?lhs" by (rule bin_of_nat_gt_0_end_True)
qed


lemma take_mod: "((w)\<^sub>2 mod 2^k) = (take k w)\<^sub>2"
proof (induction w arbitrary: k)
  case (Cons a w)
  show ?case proof (cases "k > 0")
    case True
    then have "k = k - 1 + 1" by force

    have "(2 * (w)\<^sub>2) mod 2 ^ k = (2 * (w)\<^sub>2) mod 2 ^ (k - 1 + 1)" by (subst \<open>k = k - 1 + 1\<close>) (rule refl)
    also have "... = (2 * (w)\<^sub>2) mod (2 * 2^(k-1))" by force
    also have "... = 2 * ((w)\<^sub>2 mod 2 ^ (k-1))" by (rule mult_mod_right[symmetric])
    also have "... = 2 * (take (k - 1) w)\<^sub>2" unfolding \<open>(w)\<^sub>2 mod 2 ^ (k-1) = (take (k-1) w)\<^sub>2\<close> ..
    finally have *: "(2 * (w)\<^sub>2) mod 2 ^ k = 2 * (take (k - 1) w)\<^sub>2" .

    show ?thesis proof (induction a)
      case True
      have "(True # w)\<^sub>2 mod 2 ^ k = (2 * (w)\<^sub>2 + 1) mod 2 ^ k" by simp
      also have "... = (1 + 2 * (w)\<^sub>2) mod 2 ^ k" by presburger
      also have "... = 1 + (2 * (w)\<^sub>2) mod (2 ^ k)" using \<open>k > 0\<close> by (subst even_succ_mod_exp) force+
      also have "... = 1 + 2 * (take (k - 1) w)\<^sub>2" unfolding * ..
      also have "... = (True # take (k - 1) w)\<^sub>2" by force
      also have "... = (take k (True # w))\<^sub>2" by (subst (2) \<open>k = k - 1 + 1\<close>) force
      finally show ?case .
    next
      case False
      have "(False # w)\<^sub>2 mod 2 ^ k = (2 * (w)\<^sub>2) mod 2 ^ k" by simp
      also have "... = 2 * (take (k - 1) w)\<^sub>2" unfolding * ..
      also have "... = (False # take (k - 1) w)\<^sub>2" by fastforce
      also have "... = (take k (False # w))\<^sub>2" by (subst (2) \<open>k = k - 1 + 1\<close>) force
      finally show ?case .
    qed
  qed \<comment> \<open>case \<^term>\<open>k = 0\<close> by\<close> simp
qed \<comment> \<open>case \<^term>\<open>w = []\<close> by\<close> simp


subsection\<open>Log and Bit-Length\<close>

lemma bit_len_eq_log2: "n > 0 \<Longrightarrow> bit_length n = nat_log 2 n + 1"
proof (induction n rule: log2_induct)
  case (div n)
  from \<open>n \<ge> 2\<close> have "n div 2 > 0" by force

  have "bit_length n = bit_length (2 * (n div 2))" using \<open>n \<ge> 2\<close>
    by (subst bin_of_nat_div2_times2_len) force+
  also have "... = bit_length (n div 2) + 1" using \<open>n \<ge> 2\<close> by (subst bit_len_double) force+
  also have "... = nat_log 2 (n div 2) + 1 + 1" unfolding div.IH ..
  also have "... = nat_log 2 (n) + 1" using log2.rec[OF \<open>n \<ge> 2\<close>] by presburger
  finally show "bit_length n = nat_log 2 n + 1" .
qed \<comment> \<open>case \<^term>\<open>n < 2\<close> by\<close> force+

lemma bit_len_eq_log_ceil: "n > 0 \<Longrightarrow> bit_length n = nat_log_ceil 2 (Suc n)"
  by (simp add: bit_len_eq_log2 nat_log_ceil_def numeral_Bit0)

lemma bit_length_eq_log:
  assumes "n > 0"
  shows "bit_length n = \<lfloor>log 2 n\<rfloor> + 1"
  using assms log2.altdef bit_len_eq_log2 by auto

lemma bit_len_eq_ceiling_of_log2: "n > 0 \<Longrightarrow> bit_length n = ceiling (log 2 (n + 1))"
  unfolding bit_len_eq_log_ceil nat_log_ceil_def apply auto
  apply (induction n rule: log2_induct)
   apply simp
  by (metis add.commute ceiling_log2_div2 diff_Suc_1 le_SucI log2.rec' of_nat_Suc
      plus_1_eq_Suc)


subsection\<open>Order\<close>

text\<open>From @{cite \<open>ch.~4.4\<close> rassOwf2017}: "we will order two words \<open>u, v \<in> \<Sigma>\<^sup>*\<close> as \<open>u \<le> v \<Longleftrightarrow> (u)\<^sub>2 \<le> (v)\<^sub>2\<close>."
  Note: defining the \<^const>\<open>less\<close> relation is necessary for \<^class>\<open>ord\<close>
  (of which \<^class>\<open>preorder\<close> is a subclass).
  As anti-symmetry is not given, no partial order (\<^class>\<open>order\<close>) can be established.\<close>

\<comment> \<open>The following approach (locale interpretation instead of class instantiation)
  is necessary as \<^typ>\<open>bin\<close> is defined as a type-synonym and not as independent type.\<close>
interpretation bin_preorder:
  preorder "\<lambda>a b. (a)\<^sub>2 \<le> (b)\<^sub>2" "\<lambda>a b. (a)\<^sub>2 < (b)\<^sub>2"
  using less_le_not_le le_refl le_trans by (rule class.preorder.intro)


subsection\<open>Number of Binary Strings of Given Length\<close>

lemma card_bin_len_eq: "card {w::bin. length w = l} = 2 ^ l"
proof -
  let ?bools = "UNIV :: bool set"
  have "card {w::bin. length w = l} = card {w. set w \<subseteq> ?bools \<and> length w = l}" by simp
  also have "... = card ?bools ^ l" by (intro card_lists_length_eq) (rule finite)
  also have "... = 2 ^ l" unfolding card_UNIV_bool ..
  finally show ?thesis .
qed

corollary finite_bin_len_eq: "finite {w::bin. length w = l}"
  using card_bin_len_eq by (intro card_ge_0_finite) presburger

corollary finite_bin_len_less: "finite {w::bin. length w < l}"
proof -
  let ?W = "\<lambda>l. {w::bin. length w = l}"
  let ?W\<^sub>L = "{?W l' | l'. l' < l}"

  have *: "{w::bin. length w < l} = \<Union> ?W\<^sub>L" by blast
  show "finite {w::bin. length w < l}" unfolding *
    using finite_bin_len_eq by (intro finite_Union) force+
qed

lemma card_bin_len_less: "card {w::bin. length w < l} = 2 ^ l - 1"
proof -
  let ?W = "\<lambda>l. {w::bin. length w = l}"
  let ?W\<^sub>L = "{?W l' | l'. l' < l}"

  have "card {w::bin. length w < l} = card (\<Union> ?W\<^sub>L)" by (intro arg_cong[where f=card]) blast
  also have "card (\<Union> ?W\<^sub>L) = sum card ?W\<^sub>L"
  proof (intro card_Union_disjoint)
    show "pairwise disjnt ?W\<^sub>L"
    proof (intro pairwiseI)
      fix x y
      assume "x \<in> ?W\<^sub>L" then obtain l\<^sub>x where l\<^sub>x: "x = ?W l\<^sub>x" by blast
      assume "y \<in> ?W\<^sub>L" then obtain l\<^sub>y where l\<^sub>y: "y = ?W l\<^sub>y" by blast

      assume "x \<noteq> y"
      then have "l\<^sub>x \<noteq> l\<^sub>y" unfolding l\<^sub>x l\<^sub>y by force
      then show "disjnt x y" unfolding l\<^sub>x l\<^sub>y disjnt_def by blast
    qed

    fix W
    assume "W \<in> ?W\<^sub>L" then obtain l\<^sub>W where "W = ?W l\<^sub>W" by blast
    show "finite W" unfolding \<open>W = ?W l\<^sub>W\<close> by (rule finite_bin_len_eq)
  qed
  also have "sum card ?W\<^sub>L = sum card (?W ` {..<l})"
    by (intro arg_cong[where f="sum card"]) (unfold lessThan_def, rule image_Collect[symmetric])
  also have "sum card (?W ` {..<l}) = sum (card \<circ> ?W) {..<l}"
  proof (intro sum.reindex inj_onI)
    fix x y
    obtain w :: bin where "length w = x" using Ex_list_of_length ..

    assume "?W x = ?W y"
    then have "w \<in> ?W x \<longleftrightarrow> w \<in> ?W y" for w by (rule arg_cong)
    then have "length w = x \<Longrightarrow> length w = y" by blast
    then show "x = y" unfolding \<open>length w = x\<close> by force
  qed
  also have "sum (card \<circ> ?W) {..<l} = (\<Sum>n<l. 2^n)" unfolding comp_def card_bin_len_eq ..
  also have "... = 2^l - 1" unfolding lessThan_atLeast0 by (rule sum_power2)
  finally show ?thesis .
qed

lemma inc_snoc_eq: "(\<And>k. xs \<noteq> replicate k True) \<Longrightarrow>
                    (inc (xs @ [True]))\<^sub>2 = ((inc xs) @ [True])\<^sub>2"
  apply (induction xs)
   apply auto
  by (metis replicate_Suc)

lemma inc_snoc_uneq: "\<exists>k. xs = replicate k True \<Longrightarrow>
                      (inc (xs @ [True]))\<^sub>2 \<noteq> ((inc xs) @ [True])\<^sub>2"
  apply (induction xs)
  apply auto
   apply (meson Cons_replicate_eq)
  by (simp add: Cons_replicate_eq)

lemma inc_snoc_eq_trues: "xs = replicate k True \<Longrightarrow>
                          ((replicate k False) @ [True, True])\<^sub>2 = ((inc xs) @ [True])\<^sub>2"
  apply (induction xs arbitrary: k)
  apply auto
  by (smt (verit, ccfv_SIG) Binary.inc.simps(2) Cons_replicate_eq append_Cons
      nat_of_bin.simps(2))

lemma rev_bin_nat_bin_rev_id [simp]: "starts_with True l \<Longrightarrow>
                                      rev (bin_of_nat (nat_of_bin (rev l))) = l"
  by (induction l) simp_all

lemma nat_of_bin_append1: "nat_of_bin (xs@[True]) =
                                  2^(length xs) + nat_of_bin xs"
  by (induction xs) simp_all

lemma inc_all_True [simp]: "inc (replicate n True) = (replicate n False)@[True]"
  by (induction n) simp_all

lemma bin_app_ge: "(xs@ys@zs)\<^sub>2 \<ge> (xs@zs)\<^sub>2"
  apply (induction xs)
   apply auto
  apply (induction ys)
  by auto

lemma ends_in_True_length_le_nat: "ends_in True xs \<Longrightarrow> length xs \<le> (xs)\<^sub>2"
  by (induction xs rule: ends_in_induct) simp_all

lemma length_bin_nat_times2: "n > 0 \<Longrightarrow> length (bin_of_nat (2 * n)) =
                              Suc (length (bin_of_nat n))"
  by (simp add: bin_of_nat_double)

lemma length_bin_of_nat_pow2: "length (bin_of_nat (2 ^ k)) = Suc k"
  apply (induction k)
   apply auto
  by (simp add: length_bin_nat_times2)

lemma length_bin_of_nat_pow2_m1: "length (bin_of_nat (2 ^ k - 1)) = k"
  apply (induction k)
  apply auto
  by (smt (verit, del_insts) One_nat_def Suc_diff_Suc Suc_eq_plus1 Suc_mask_eq_exp
      Suc_pred add_Suc_right bin_nat_bin bin_of_nat.simps(1) bin_of_nat.simps(2)
      bit_len_gt_0_iff diff_zero length_append length_bin_nat_times2
      length_bin_of_nat_pow2 length_greater_0_conv less_add_Suc1 less_not_refl
      less_numeral_extra(1) list.size(3) list.size(4) mult_2 nat_bin_nat
      nat_of_bin.simps(1) nat_of_bin_app1 plus_1_eq_Suc pos2 right_diff_distrib'
      zero_less_diff zero_less_power)

lemma length_bin_of_bin_leI: "n \<le> m \<Longrightarrow>
                              length (bin_of_nat n) \<le> length (bin_of_nat m)"
  apply (induction n arbitrary: m)
proof auto
  fix na :: nat and ma :: nat
  assume a1: "Suc na \<le> ma"
  have "\<forall>n. length (bin_of_nat n) \<le> length (bin_of_nat (Suc n))"
    by (simp add: inc_len)
  then have "length (bin_of_nat (Suc na)) \<le> length (bin_of_nat ma)"
    using a1 by (meson lift_Suc_mono_le)
  then show "length (inc (bin_of_nat na)) \<le> length (bin_of_nat ma)"
    by simp
qed

lemma length_bin_of_nat_le_iff: "length (bin_of_nat n) \<le> k \<longleftrightarrow> n < 2 ^ k"
  apply standard
  using length_bin_of_nat_pow2
   apply (metis dual_order.strict_trans leD linorder_cases log2.valid_base
      nat_bin_nat nat_of_bin_max power_strict_increasing_iff)
  using length_bin_of_bin_leI length_bin_of_nat_pow2_m1
  by (metis Suc_leI Suc_mask_eq_exp add_diff_cancel_left' add_le_imp_le_left
      plus_1_eq_Suc)

lemma bij_betw_nat_of_bin: "bij_betw nat_of_bin {w. ends_in True w} {n. n > 0}"
proof -
  have "ends_in True w \<Longrightarrow> ends_in True w' \<Longrightarrow> nat_of_bin w = nat_of_bin w' \<Longrightarrow>
        w = w'" for w w' :: bin
    apply (induction w arbitrary: w' rule: ends_in_induct)
     apply auto
     apply (metis Binary.inc.simps(1) append_self_conv2 bin_nat_bin
        bin_of_nat.simps(1) bin_of_nat.simps(2))
    by (metis append_Cons bin_nat_bin butlast_snoc nat_of_bin.simps(2))
  moreover have "n > 0 \<Longrightarrow> \<exists>w. nat_of_bin w = n \<and> ends_in True w" for n :: nat
    using nat_bin_nat by blast
  ultimately show ?thesis by (metis bij_nat_of_bin greaterThan_def)
qed

lemma Suc_length_bin_of_nat_iff: "length (bin_of_nat (Suc n)) =
                                  Suc (length (bin_of_nat n)) \<longleftrightarrow>
                                  (\<exists>k. Suc n = 2 ^ k)"
  by (metis Suc_lessI Suc_n_not_le_n diff_Suc_1 length_bin_of_nat_le_iff
      length_bin_of_nat_pow2 length_bin_of_nat_pow2_m1 nat_bin_nat nat_of_bin_max)

lemma nat_of_bin_suff_ge_iff: "(xs1@xs2)\<^sub>2 \<le> (xs1@xs2')\<^sub>2 \<longleftrightarrow> (xs2)\<^sub>2 \<le> (xs2')\<^sub>2"
  by (induction xs1) simp_all

lemma nat_of_bin_suff_diff: "(xs2)\<^sub>2 < (xs2')\<^sub>2 \<Longrightarrow>
                             (xs1@xs2')\<^sub>2 - (xs1@xs2)\<^sub>2 \<ge> 2 ^ length xs1"
  by (induction xs1) simp_all

lemma nat_of_bin_gt_eq_p_length: "length xs1 = length xs1' \<Longrightarrow>
                                  (xs2)\<^sub>2 < (xs2')\<^sub>2 \<Longrightarrow> (xs1@xs2)\<^sub>2 < (xs1'@xs2')\<^sub>2"
proof (induction xs1 arbitrary: xs1')
  case Nil
  then show ?case by simp
next
  case IH: (Cons a xs1)
  obtain h :: bool and t :: bin where xs1'_def: "xs1' = h#t" using IH(2)
    by (metis hd_Cons_tl length_0_conv)
  have "length xs1 = length t" using IH(2) unfolding xs1'_def by simp
  hence 1: "(xs1 @ xs2)\<^sub>2 < (t @ xs2')\<^sub>2" by (rule IH(1)) (rule IH(3))
  have 2: "h \<Longrightarrow> a \<Longrightarrow> ?case" unfolding xs1'_def apply simp
    by (rule 1)
  have 3: "\<not>h \<Longrightarrow> a \<Longrightarrow> ?case" unfolding xs1'_def using 1 by simp
  have 4: "\<not>h \<Longrightarrow> \<not>a \<Longrightarrow> ?case" unfolding xs1'_def apply simp
    by (rule 1)
  have 5: "h \<Longrightarrow> \<not>a \<Longrightarrow> ?case" unfolding xs1'_def using 1 by simp
  show ?case using 2 3 4 5 by auto
qed

lemma length_bin_of_nat_between: "ends_in True xs1 \<Longrightarrow> ends_in True xs2 \<Longrightarrow>
                                  ends_in True xs3 \<Longrightarrow> length xs1 = length xs2 \<Longrightarrow>
                                  (xs3)\<^sub>2 \<le> (xs2)\<^sub>2 \<Longrightarrow> (xs1)\<^sub>2 \<le> (xs3)\<^sub>2 \<Longrightarrow>
                                  length xs3 = length xs1"
  by (metis less_le_not_le nat_neq_iff nat_of_bin_len_mono)

lemma suffix_bin_of_nat_between: "suffix x xs1 \<Longrightarrow> suffix x xs2 \<Longrightarrow>
                                  ends_in True xs1 \<Longrightarrow> ends_in True xs2 \<Longrightarrow>
                                  ends_in True xs3 \<Longrightarrow> length xs1 = length xs2 \<Longrightarrow>
                                  (xs3)\<^sub>2 \<le> (xs2)\<^sub>2 \<Longrightarrow> (xs1)\<^sub>2 \<le> (xs3)\<^sub>2 \<Longrightarrow>
                                  suffix x xs3"
proof -
  assume a1: "suffix x xs1" and a2: "suffix x xs2" and a3: "\<exists>ys. xs1 = ys @ [True]"
     and a4: "\<exists>ys. xs2 = ys @ [True]" and a5: "\<exists>ys. xs3 = ys @ [True]" and
         a6: "length xs1 = length xs2" and a7: "(xs3)\<^sub>2 \<le> (xs2)\<^sub>2" and
         a8: "(xs1)\<^sub>2 \<le> (xs3)\<^sub>2"
  obtain p1 p2 :: bin where xs1_def: "xs1 = p1 @ x" and xs2_def: "xs2 = p2 @ x"
    using a1 a2 by (meson suffixE)
  have 1: "length p1 = length p2" using a6 unfolding xs1_def xs2_def by simp
  have xs1_le_xs2: "(xs1)\<^sub>2 \<le> (xs2)\<^sub>2" using a7 a8 by simp
  have 2: "length xs1 = length xs3"
    by (metis a3 a4 a5 a6 a7 a8 length_bin_of_nat_between)
  have "\<not>suffix x xs3 \<Longrightarrow> False"
  proof -
    assume a9: "\<not>suffix x xs3"
    define x' :: bin where "x' \<equiv> drop (length xs3 - length x) xs3"
    have 3: "length x' = length x" unfolding x'_def using a1 2
      by (metis drop_diff_length suffix_length_le)
    have 4: "suffix x' xs3" unfolding x'_def by (rule suffix_drop)
    define p :: bin where "p \<equiv> take (length xs3 - length x) xs3"
    have 5: "p@x' = xs3" unfolding p_def x'_def by simp
    have 6: "x' \<noteq> x" using a9 4 by simp
    have 7: "(x')\<^sub>2 \<noteq> (x)\<^sub>2" by (metis 3 6 append_same_eq bin_nat_bin nat_of_bin_app)
    have 8: "length p = length p1" using 2 3 5 xs1_def by force
    have 9: "(x')\<^sub>2 < (x)\<^sub>2 \<Longrightarrow> (p@x')\<^sub>2 < (p1@x)\<^sub>2"
      by (rule nat_of_bin_gt_eq_p_length) (rule 8)
    have 10: "(x')\<^sub>2 > (x)\<^sub>2 \<Longrightarrow> (p@x')\<^sub>2 > (p2@x)\<^sub>2"
      apply (rule nat_of_bin_gt_eq_p_length)
      using 1 8 by presburger
    show False using 5 7 9 10 a7 a8 xs1_def xs2_def by force
  qed
  thus "suffix x xs3" by blast
qed

lemma length_bin_of_nat_dsqrt [simp]: "length (bin_of_nat (dsqrt n)) =
                                        Suc (length (bin_of_nat n)) div 2"
proof (induction n)
  case 0
  then show ?case by simp
next
  case IH: (Suc n)
  have 1: "dsqrt (2 ^ (2 * k)) = 2 ^ k" for k :: nat
    by (simp add: power_even_eq)
  have "Suc n = 2 ^ (2 * k) \<Longrightarrow> ?case" for k :: nat
    apply (simp add: 1)
    using div2_Suc_Suc div_mult_self1_is_m length_bin_of_nat_pow2 pos2 by presburger
  moreover have "(\<And>k. Suc n \<noteq> 2 ^ (2 * k)) \<Longrightarrow> ?case"
  proof -
    assume a1: "\<And>k. Suc n \<noteq> 2 ^ (2 * k)"
    have "n > 0" using a1
      by (metis bot_nat_0.not_eq_extremum mult_eq_0_iff nat_power_eq_Suc_0_iff)
    have 2: "n = 1 \<Longrightarrow> Suc (length (bin_of_nat (dsqrt (Suc n)))) div 2 =
             Suc (Suc (length (bin_of_nat (Suc n))) div 2) div 2" apply simp
      by (metis length_bin_of_nat_pow2 less_exp numeral_2_eq_2 numeral_Bit0_div_2
          numerals(1) power_0 power_Suc_0 floor_sqrt_unique suc_is_ge)
    have 3: "n = 2 \<Longrightarrow> Suc (length (bin_of_nat (dsqrt (Suc n)))) div 2 =
             Suc (Suc (length (bin_of_nat (Suc n))) div 2) div 2" apply simp
      by (metis One_nat_def Suc_eq_plus1 add_Suc_shift bin_of_nat_double_p1
          bits_1_div_2 diff_Suc_Suc diff_zero div2_Suc_Suc length_Cons
          length_bin_of_nat_pow2 mult.right_neutral mult_2_right next_sq_def
          next_sq_eq numeral_2_eq_2 numeral_3_eq_3 power2_eq_square power_0
          floor_sqrt_inverse_power2 zero_less_Suc)
    have 4: "n \<noteq> 3" using a1
      by (metis Suc_1 add_2_eq_Suc mult_2_right numeral_1_eq_Suc_0 numeral_3_eq_3
          numeral_One power2_eq_square power_even_eq power_one_right)
    have 5: "n \<ge> 4 \<Longrightarrow> length (bin_of_nat (dsqrt (Suc n))) =
             length (bin_of_nat (dsqrt n))" using a1 Suc_length_bin_of_nat_iff
      by (metis bin_of_nat.simps(2) length_inc_cases power_even_eq floor_sqrt_Suc
          floor_sqrt_inverse_power2)
    show "length (bin_of_nat (dsqrt (Suc n))) =
          Suc (length (bin_of_nat (Suc n))) div 2"
      apply (cases "n \<ge> 4")
      unfolding 5 unfolding IH using a1 Suc_length_bin_of_nat_iff
       apply (metis One_nat_def bin_of_nat.simps(2) diff_Suc_1' even_Suc_div_two
          length_bin_of_nat_pow2_m1 length_inc_cases odd_two_times_div_two_nat)
      by (smt (verit) IH One_nat_def Suc_length_bin_of_nat_iff bin_of_nat.simps(2)
          calculation diff_Suc_1' even_Suc_div_two length_bin_of_nat_pow2
          length_inc_cases odd_two_times_div_two_nat power_even_eq floor_sqrt_Suc
          floor_sqrt_inverse_power2)
  qed
  ultimately show ?case by blast
qed

lemma length_bin_of_nat_2np1_lower_bound: "length (bin_of_nat (2 * n + 1)) \<ge>
                                            length (bin_of_nat n)"
  apply simp
  by (metis inc_len length_bin_of_bin_leI mult_2 nat_le_iff_add order.trans)

lemma length_bin_of_nat_2np1_upper_bound: "length (bin_of_nat (2 * n + 1)) \<le>
                                           Suc (length (bin_of_nat n))"
  using bin_of_nat_double_p1 by auto

lemma length_diff_next_square_bin: "length (bin_of_nat (next_square n - n)) \<le>
                                    Suc (Suc (length (bin_of_nat n)) div 2)"
proof -
  have "length (bin_of_nat (next_square n - n)) \<le>
        length (bin_of_nat (2 * dsqrt n + 1))"
    by (fact length_bin_of_bin_leI [OF next_sq_diff])
  also have "... \<le> Suc (Suc (length (bin_of_nat n)) div 2)"
    apply (cases "length (bin_of_nat (2 * dsqrt n + 1)) =
                  length (bin_of_nat (dsqrt n))")
     apply (erule ssubst)
     apply (subst length_bin_of_nat_dsqrt)
     apply simp
  proof -
    assume a1: "length (bin_of_nat (2 * dsqrt n + 1)) \<noteq>
                length (bin_of_nat (dsqrt n))"
    moreover have "dsqrt n \<le> 2 * dsqrt n + 1" by simp
    ultimately have "length (bin_of_nat (2 * dsqrt n + 1)) =
                     Suc (length (bin_of_nat (dsqrt n)))"
      using length_bin_of_bin_leI length_bin_of_nat_2np1_upper_bound
      by (meson le_Suc_eq le_antisym)
    thus "length (bin_of_nat (2 * dsqrt n + 1))
          \<le> Suc (Suc (length (bin_of_nat n)) div 2)"
      using le_refl length_bin_of_nat_dsqrt by presburger
  qed
  finally show ?thesis .
qed

lemma bin_app_sub_same_prefix: "(xs@ys)\<^sub>2 - (xs@zs)\<^sub>2 =
       (replicate (length xs) False @ (bin_of_nat ((ys)\<^sub>2 - (zs)\<^sub>2)))\<^sub>2"
  by (induction xs) simp_all

lemma  "(True#True#xs)\<^sub>2 > (b#False#xs)\<^sub>2"
  by simp

lemma nat_of_bin_app_le: "length p1 = length p2 \<Longrightarrow> (p1)\<^sub>2 \<ge> (p2)\<^sub>2 \<Longrightarrow>
                          (p1@xs)\<^sub>2 \<ge> (p2@xs)\<^sub>2"
  by (simp add: nat_of_bin_app)

lemma bit_length_sub: "bit_length (n - m) \<le> bit_length n"
  by (simp add: length_bin_of_bin_leI)

lemma bin_of_nat_app_mod [simp]: "(xs@ys)\<^sub>2 mod 2^(length xs) = (xs)\<^sub>2"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (simp add: Suc_double_not_eq_double mod_Suc)
qed

lemma nat_of_bin_length_mono: "(xs1)\<^sub>2 \<le> (xs2)\<^sub>2 \<Longrightarrow> ends_in True xs1 \<Longrightarrow>
                               length xs1 \<le> length xs2"
  apply (induction xs1)
   apply auto
  by (metis length_Cons linorder_not_le nat_of_bin.simps(2) nat_of_bin_len_mono)

lemma nat_of_bin_length_mono2: "bit_length n1 < bit_length n2 \<Longrightarrow> n1 < n2"
  apply (induction n1)
   apply auto
  using bin_of_nat.simps(1) bot_nat_0.not_eq_extremum apply blast
  by (metis Suc_leI inc_Suc inc_len len_bin_nat_bin less_le_not_le nat_bin_nat
      order_le_less_trans order_neq_le_trans)

lemma replicate_True_ge: "(replicate (length w) True)\<^sub>2 \<ge> (w)\<^sub>2"
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case by simp
qed

lemma bit_length_sum_prefix_eq: "prefix (replicate n False) xs \<Longrightarrow> ends_in True xs \<Longrightarrow>
                                 length ys \<le> n \<Longrightarrow> bit_length ((xs)\<^sub>2 + (ys)\<^sub>2) = length xs"
proof (induction xs arbitrary: n ys)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a zs)
  then show ?case apply auto
    apply (metis Cons_replicate_eq)
      apply (metis (no_types, lifting) Binary.inc.simps(1) Cons_replicate_eq IH.prems(1)
        add.right_neutral bin_nat_bin bin_of_nat.simps(2) bit_len_gt_0_iff leD length_Cons
        length_greater_0_conv length_replicate list.size(3) nat_0_less_mult_iff nat_bin_nat
        nat_of_bin.simps(1) nat_of_bin.simps(2) plus_1_eq_Suc prefix_Cons)
     apply (metis less_numeral_extra(3) nat_of_bin_0s nat_of_bin_gt_0_end_True)
  proof -
    fix as :: bin
    assume a1: "\<And>n ys. prefix (False \<up> n) zs \<Longrightarrow> \<exists>ys. zs = ys @ [True] \<Longrightarrow>
                length ys \<le> n \<Longrightarrow> length (bin_of_nat ((zs)\<^sub>2 + (ys)\<^sub>2)) = length zs" and
           a2: "length ys \<le> n" and a3: "False # zs = as @ [True]" and
           a4: "prefix (False \<up> n) as"
    have 1: "prefix (False \<up> (n - 1)) zs" using a3 a4
      by (metis Cons_prefix_Cons[of _ _ False zs] Nil_prefix[of zs] list.sel(3) nat_of_bin.cases[of "False \<up> n"]
          prefix_prefix[of "_ # _" as "[True]"] replicate_0[of undefined] tl_replicate[of n False]
          tl_replicate[of "0" undefined] zero_diff[of "1"])
    have 2: "\<exists>ys. zs = ys @ [True]" using a3 by (metis ends_in_Cons last.simps last_snoc)
    note a1 [OF 1 2, of "tl ys"]
    hence 3: "length (bin_of_nat ((zs)\<^sub>2 + (tl ys)\<^sub>2)) = length zs"
      apply this
      using a2 by simp
    have "ys = [] \<Longrightarrow> length (bin_of_nat (2 * (zs)\<^sub>2 + (ys)\<^sub>2)) = Suc (length zs)"
      by (simp add: 2 length_bin_nat_times2)
    moreover have "ys \<noteq> [] \<Longrightarrow> length (bin_of_nat (2 * (zs)\<^sub>2 + (ys)\<^sub>2)) = Suc (length zs)"
    proof -
      assume "ys \<noteq> []"
      then obtain h :: bool and t :: bin where ys_def: "ys = h#t"
        using list.exhaust_sel by blast
      have 4: "tl ys = t" unfolding ys_def by simp
      have 5: "length (bin_of_nat ((zs)\<^sub>2 + (t)\<^sub>2)) = length zs" using 3 unfolding 4 .
      have "h \<Longrightarrow> length (bin_of_nat (2 * (zs)\<^sub>2 + (ys)\<^sub>2)) = Suc (length zs)"
        unfolding ys_def apply simp
        by (metis 2 5 Suc_eq_plus1 add_gr_0 bin_of_nat.simps(2) bit_len_even_odd
            distrib_left_numeral length_bin_nat_times2 nat_of_bin_gt_0_end_True)
      moreover have "\<not>h \<Longrightarrow> length (bin_of_nat (2 * (zs)\<^sub>2 + (ys)\<^sub>2)) = Suc (length zs)"
        unfolding ys_def apply simp
        by (metis 2 5 add_gr_0 distrib_left_numeral length_bin_nat_times2
            nat_of_bin_gt_0_end_True)
      ultimately show "length (bin_of_nat (2 * (zs)\<^sub>2 + (ys)\<^sub>2)) = Suc (length zs)" by blast
    qed
    ultimately show "length (bin_of_nat (2 * (zs)\<^sub>2 + (ys)\<^sub>2)) = Suc (length zs)" by blast
  qed
qed

definition msb_index :: "bin \<Rightarrow> nat" where
  "msb_index b \<equiv> last_with_index id b"

lemma msb_index_bin_of_nat [simp]: "msb_index (bin_of_nat n) = bit_length n - 1"
proof (induction "bin_of_nat n" arbitrary: n)
  case Nil
  then show ?case by (simp add: msb_index_def)
next
  case IH: (Cons a x)
  have 1: "x = bin_of_nat (n div 2)" using IH(2) by (metis bin_of_nat_div2 list.sel(3))
  note 2 = IH(1) [OF 1]
  then show ?case unfolding msb_index_def apply (simp add: bin_of_nat_div2)
    by (smt (z3) 1 IH(2) One_nat_def Suc_pred' 2 bin_of_nat_div2 id_def
        last_conv_nth_default last_with_index_Cons1 last_with_index_Cons2
        last_with_index_none length_0_conv length_butlast length_greater_0_conv length_tl
        less_zeroE msb_index_def nat_bin_nat nat_of_bin_app0 nth_default_def
        snoc_eq_iff_butlast)
qed

lemma bit_length_mult_pow2: "n > 0 \<Longrightarrow> bit_length (n * 2^k) = bit_length n + k"
  apply (induction k)
   apply auto
  by (metis length_bin_nat_times2 mult.left_commute mult_pos_pos pos2 zero_less_power)

lemma bit_length_div_pow2: "bit_length (n div 2^k) = bit_length n - k"
  apply (induction k)
   apply auto
  by (metis Suc_eq_plus1 bin_of_nat_div2 diff_diff_left div_mult2_eq length_tl mult.commute)

lemma take_mult_pow2: "n > 0 \<Longrightarrow> take k (bin_of_nat (n * 2^k)) = (replicate k False)"
  apply (induction k)
   apply auto
  by (metis bin_of_nat_double mult.left_commute mult_pos_pos pos2 take_Suc_Cons
      zero_less_power)

lemma bit_length_div_mult_eq: "(x::nat) \<ge> 2^y \<Longrightarrow>
                               bit_length (x div 2^y * 2^y) = bit_length x"
proof (induction y)
  case 0
  then show ?case by simp
next
  case (Suc y)
  hence "length (bin_of_nat (x div 2 ^ y * 2 ^ y)) = length (bin_of_nat x)" by simp
  then show ?case using Suc(2)
    by (metis bit_len_eq_0_iff bit_length_div_pow2 bit_length_mult_pow2 le_add_diff_inverse2
        length_bin_of_nat_le_iff linorder_not_less order_less_le plus_nat.add_0
        zero_less_iff_neq_zero)
qed

lemma take_bin_of_nat_sum: "(take k (bin_of_nat (x + y)))\<^sub>2 =
                            (take k (bin_of_nat ((take k (bin_of_nat x))\<^sub>2 +
                            (take k (bin_of_nat y))\<^sub>2)))\<^sub>2"
  unfolding take_mod [symmetric] by simp presburger

lemma bit_length_div_2 [simp]: "bit_length (n div 2) = (bit_length n) - 1"
  by (simp add: bin_of_nat_div2)

lemma n_le_pow2_bit_length: "2^(bit_length n) \<ge> n"
  by (meson length_bin_of_nat_le_iff less_or_eq_imp_le)

lemma bit_length_eq_iff: "bit_length x = Suc k \<longleftrightarrow> x \<ge> 2^k \<and> x < 2^(Suc k)"
  by (metis Suc_n_not_le_n le_SucE length_bin_of_nat_le_iff nle_le verit_comp_simplify1(3))

lemma bit_length_pow2_add: "x < 2^k \<Longrightarrow> bit_length (2^k + x) = Suc k"
  unfolding bit_length_eq_iff by simp

lemma bit_length_pow2_mult_add: "x < 2^k \<Longrightarrow> y > 0 \<Longrightarrow>
                                 bit_length (2^k * y + x) = bit_length y + k"
proof -
  assume a1: "x < 2^k" and a2: "y > 0"
  define k' :: nat where "k' \<equiv> k + bit_length y - 1"
  have 1: "2^k' \<le> 2^k * y" unfolding k'_def
    by (metis Suc_diff_1 a2 add.commute bit_len_gt_0_iff bit_length_eq_iff
        bit_length_mult_pow2 mult.commute trans_less_add2)
  have 2: "bit_length y > 0" using a2 bit_len_gt_0_iff by auto
  have 3: "2 ^ Suc (k + length (bin_of_nat y) - 1) = 2 ^ (k + length (bin_of_nat y))"
    using 2 by simp
  have 4: "2^Suc k' \<ge> 2^k * y" unfolding k'_def 3
    by (simp add: n_le_pow2_bit_length power_add)
  define x' :: nat where "x' \<equiv> 2^k * y - 2^k' + x"
  have 5: "2^k * y + x = 2^k' + x'" unfolding k'_def x'_def apply simp
    by (metis 1 One_nat_def k'_def le_add_diff_inverse)
  have 6: "2 ^ k * y + x < 2 ^ (k + length (bin_of_nat y))" using a1 a2
  proof (induction "bin_of_nat y" arbitrary: y rule: list_length_full_induct)
    case 1
    hence 2: "length (bin_of_nat y) - Suc 0 < length (bin_of_nat y)"
      using bin_of_nat_len_gt_0 diff_Suc_less by presburger
    note 3 = 1(1) [of "y div 2", simplified, OF 2 1(2)]
    have "0 < y div 2 \<Longrightarrow> ?case"
    proof -
      assume a3: "0 < y div 2"
      note 3 = 3 [OF a3]
      have lt: "2 ^ (k + length (bin_of_nat y) - Suc 0) + 2^k * y div 2 <
                2 ^ (k + length (bin_of_nat y))"
        by (metis (no_types, lifting) "1.prems"(2) Nat.add_diff_assoc One_nat_def
            Suc_pred a3 add.commute add_gr_0 bin_of_nat_len_gt_0 bit_length_div_2
            bit_length_eq_iff bit_length_mult_pow2 bit_length_pow2_add length_Suc0_not_empty
            length_greater_0_conv mult.commute)
      have "even y \<Longrightarrow> ?case"
      proof -
        assume a4: "even y"
        hence 4: "2 ^ k * y = 2 ^ k * y div 2 + 2 ^ k * y div 2" by auto
        have 5: "2 ^ k * (y div 2) = 2 ^ k * y div 2" using a4 div_mult_swap by blast
        have "2 ^ k * y + x < 2 ^ (k + length (bin_of_nat y) - Suc 0) + 2^k * y div 2"
          using 3 apply (subst 4)
          apply auto
          unfolding 5 using 1(3) bin_of_nat_len_gt_0 by auto
        also have "... < 2 ^ (k + length (bin_of_nat y))" by fact
        finally show ?case .
      qed
      moreover have "odd y \<Longrightarrow> ?case"
      proof -
        assume a4: "odd y"
        have "k = 0 \<Longrightarrow> ?case" apply simp
          by (metis One_nat_def a1 add.right_neutral less_one nat_bin_nat nat_of_bin_max
              nat_power_eq_Suc_0_iff)
        moreover have "k > 0 \<Longrightarrow> ?case"
        proof -
          assume a5: "k > 0"
          hence 4: "2 ^ k * y = 2 ^ k * y div 2 + 2 ^ k * y div 2"
            by (metis even_mult_iff even_numeral even_power even_two_times_div_two mult_2)
          have 5: "2 ^ k * (y div 2) = 2 ^ k * y div 2 - 2^(k - 1)" using a5
          proof (induction k)
            case 0
            then show ?case by simp
          next
            case (Suc k)
            then show ?case apply auto
              by (smt (verit) One_nat_def a4 mult.assoc mult.commute mult_numeral_1_right
                  numeral_1_eq_Suc_0 odd_n_div_mult2 right_diff_distrib')
          qed
          have 6: "2 ^ k * y div 2 \<ge> 2 ^ (k - Suc 0)"
            by (metis 5 One_nat_def a3 diff_is_0_eq divisors_zero less_numeral_extra(3)
                nat_le_linear nat_zero_less_power_iff power_not_zero zero_power2)
          have "2 ^ k * y + x < 2 ^ (k + length (bin_of_nat y) - Suc 0) +
                2^k * y div 2 + 2^(k - 1)"
            using 3 apply (subst 4)
            apply auto
            unfolding 5 using 6 apply auto
            using "1.prems"(2) bit_len_gt_0_iff by force
          also have "... \<le> 2 ^ (k + length (bin_of_nat y))"
          proof -
            have 1: "2 ^ k * y div 2 < 2 ^ (k + length (bin_of_nat y) - 1)"
              by (metis "1.prems"(2) add.commute bit_length_div_2 bit_length_mult_pow2
                  eq_imp_le length_bin_of_nat_le_iff mult.commute)
            have 2: "y \<ge> 3"
              by (metis Suc_leI a3 a4 div_less even_numeral linorder_neqE_nat not_gr0
                  numeral_2_eq_2 numeral_3_eq_3)
            have 3: "2 ^ (k - 1) < 2 ^ k * y div 2"
              by (metis 5 6 One_nat_def a3 diff_self_eq_0 le_eq_less_or_eq
                  less_numeral_extra(3) mult_is_0 nat_zero_less_power_iff pos2)
            have 4: "(2::nat)^(k - 1) < 2^k" using \<open>k > 0\<close> by simp
            have 5: "2 ^ k * y div 2 = 2 ^ (k - 1) * y"
              by (metis One_nat_def Suc_leI a5 dvd_div_mult dvd_power less_numeral_extra(3)
                  nat_zero_less_power_iff power_diff_power_eq power_one_right zero_power2)
            have 6: "2 ^ (k + length (bin_of_nat y) - Suc 0) - 2 ^ k * y div 2 \<ge>
                     2 ^ (k - 1)"
            proof (induction k)
              case 0
              then show ?case apply simp
                by (metis One_nat_def bit_length_div_2 dvd_1_left dvd_imp_le eq_imp_le
                    length_bin_of_nat_le_iff zero_less_diff)
            next
              case (Suc k)
              show ?case
              proof (cases "k = 0")
                case True
                then show ?thesis
                  using length_bin_of_nat_le_iff less_eq_Suc_le zero_less_diff by auto
              next
                case False
                hence "(2::nat) ^ (Suc k + length (bin_of_nat y) - Suc 0) -
                      2 ^ Suc k * y div 2 =
                      2 * (2 ^ (k + length (bin_of_nat y) - Suc 0) - 2 ^ k * y div 2)"
                  by (smt (verit, del_insts) One_nat_def ab_semigroup_add_class.add_ac(1)
                      ab_semigroup_mult_class.mult_ac(1) diff_add_inverse
                      diff_mult_distrib2 div_mult_swap dvd_mult2 dvd_power less_SucE
                      less_numeral_extra(1) plus_1_eq_Suc power_commuting_commutes
                      power_minus_mult trans_less_add1)
                then show ?thesis apply simp using Suc
                  by (metis False Suc_1 Suc_mult_le_cancel1 power_eq_if)
              qed
            qed
            have 7: "(2::nat) ^ (k + length (bin_of_nat y)) =
                     2 ^ (k + length (bin_of_nat y) - Suc 0) +
                     2 ^ (k + length (bin_of_nat y) - Suc 0)"
              by (metis One_nat_def a5 add_gr_0 mult_2_right power_minus_mult)
            show "2 ^ (k + length (bin_of_nat y) - Suc 0) + 2 ^ k * y div 2 + 2 ^ (k - 1)
                  \<le> 2 ^ (k + length (bin_of_nat y))" apply (subst 7)
              apply simp
              using 6 1 3
              by (metis Nat.le_diff_conv2 One_nat_def add.commute less_imp_le_nat)
          qed
          finally show ?case .
        qed
        ultimately show ?case by blast
      qed
      ultimately show ?case by auto
    qed
    moreover have "y = 0 \<Longrightarrow> ?case" by (simp add: 1(2))
    moreover have "y = 1 \<Longrightarrow> ?case" by (simp add: 1(2))
    ultimately show ?case by linarith
  qed
  have 7: "x' < 2^k'" unfolding x'_def k'_def apply simp
    using 6 by (metis 3 5 One_nat_def k'_def mult_2 nat_add_left_cancel_less power_Suc
        x'_def)
  note 8 = bit_length_pow2_add [OF 7]
  show "length (bin_of_nat (2 ^ k * y + x)) = length (bin_of_nat y) + k"
    using 8 unfolding k'_def x'_def apply simp
    by (metis 2 5 8 Suc_diff_1 add.commute k'_def neq0_conv not_add_less1)
qed

lemma bit_length_bin_add_eq: "take k w = replicate k False \<Longrightarrow> bit_length x \<le> k \<Longrightarrow>
                              (w)\<^sub>2 > x \<Longrightarrow> bit_length ((w)\<^sub>2 + x) = bit_length (w)\<^sub>2"
proof -
  assume a1: "take k w = False \<up> k" and a2: "length (bin_of_nat x) \<le> k" and
         a3: "x < (w)\<^sub>2"
  have 1: "(w)\<^sub>2 = 2^k * (drop k w)\<^sub>2"
    using a1 by (metis append_take_drop_id mult.commute nat_of_bin_app_0s)
  have 2: "x < 2^k" using a2 length_bin_of_nat_le_iff by auto
  have "(drop k w)\<^sub>2 \<noteq> 0" using a2 a3 by (metis 1 mult_0_right not_less_zero)
  hence 3: "(drop k w)\<^sub>2 > 0" by simp
  note 4 = bit_length_pow2_mult_add [OF 2 3, folded 1]
  show "bit_length ((w)\<^sub>2 + x) = bit_length (w)\<^sub>2" using 4
    by (simp add: 1 3 bit_length_mult_pow2 mult.commute)
qed

lemma bit_length_div_mult_eq': "x \<ge> 2^y \<Longrightarrow> bit_length ((x div 2^y) * 2^y) = bit_length x"
  using bit_length_div_mult_eq le_eq_less_or_eq by auto

lemma bin_of_nat_pow2 [simp]: "bin_of_nat (2^k) = (replicate k False)@[True]"
  by (metis add.right_neutral bin_nat_bin length_replicate nat_of_bin_0s
      nat_of_bin_append1)

lemma bin_of_nat_div_pow2: "bin_of_nat (x div 2^k) = drop k (bin_of_nat x)"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case apply simp
    by (metis add.commute bin_of_nat_div2 div_mult2_eq drop0 drop_Suc drop_drop mult.commute)
qed

lemma div_pow2_summand_vanish:
  assumes "bit_length n \<le> k" and "bit_length n \<le> l"
  shows "(x * 2^k + n) div 2^l = (x * 2^k) div 2^l"
  unfolding nat_div_pow2_distribute [OF assms(1) [unfolded length_bin_of_nat_le_iff]]
  using assms(2) [unfolded length_bin_of_nat_le_iff] by simp

(* Replicate lemmas from above that are used for an encoding of binary digits using booleans
   and now use boolean lists. *)

type_synonym bin' = "bool list list"

definition separator :: "bool list" ("$") where "$ \<equiv> [False, True]"

fun bin_of_bin' :: "bin' \<Rightarrow> bin" where
  "bin_of_bin' b' = map (\<lambda>b'. hd b') b'"

fun bin'_of_bin :: "bin \<Rightarrow> bin'" where
  "bin'_of_bin b = map (\<lambda>b. [b]) b"

fun bin'_of_nat :: "nat \<Rightarrow> bin'" where
  "bin'_of_nat n = bin'_of_bin (bin_of_nat n)"

fun nat_of_bin' :: "bin' \<Rightarrow> nat" where
  "nat_of_bin' b' = nat_of_bin (bin_of_bin' b')"

fun inc' :: "bin' \<Rightarrow> bin'" where
  "inc' b' = bin'_of_bin (inc (bin_of_bin' b'))"

lemma bin'_of_bin_inv [simp]: "bin_of_bin' (bin'_of_bin b) = b"
  by simp

lemma bin'_cases: "(\<forall>s\<in>set b'. \<exists>x. s = [x]) \<longleftrightarrow> (\<forall>s\<in>set b'. s = [True] \<or> s = [False])"
  by auto

lemma bin_of_bin'_inv: "(\<forall>s\<in>set b'. \<exists>x. s = [x]) \<Longrightarrow> bin'_of_bin (bin_of_bin' b') = b'"
  apply auto
  by (metis (no_types, lifting) comp_apply list.sel(1) map_idI)

lemma inc'_not_Nil: "inc' xs \<noteq> []" by (induction xs) auto
lemma inc'_Suc: "Suc (nat_of_bin' xs) = nat_of_bin' (inc' xs)" apply (induction xs)
  by auto
lemma inc'_inc': "(\<forall>s\<in>set xs. \<exists>x. s = [x]) \<Longrightarrow> x = [True] \<or> x = [False] \<Longrightarrow>
                  xs \<noteq> [] \<Longrightarrow> inc' (inc' (x # xs)) = x # (inc' xs)"
  apply (induction xs)
   apply simp_all
  by fastforce

lemma nat_of_bin'_app0: "nat_of_bin' (xs @ [[False]]) = nat_of_bin' xs"
  by (induction xs) auto
lemma nat_of_bin'_app1: "nat_of_bin' (xs @ [[True]]) = nat_of_bin' xs + 2 ^ length xs"
  by (induction xs) auto

lemma nat_of_bin'_app: "nat_of_bin' (lo @ up) = (nat_of_bin' up) * 2^(length lo) + (nat_of_bin' lo)"
  by (induction lo) auto

lemma nat_of_bin'_0s [simp]: "nat_of_bin' ([False] \<up> k) = 0" by (induction k) auto
corollary nat_of_bin'_app_0s: "nat_of_bin' ([False] \<up> k @ up) = (nat_of_bin' up) * 2^k"
  using nat_of_bin_app by simp
corollary nat_of_bin'_leading_0s[simp]: "nat_of_bin' (xs @ [False] \<up> k) = nat_of_bin' xs"
  using nat_of_bin'_app by simp

lemma hd'_one_nonzero: "nat_of_bin' ([True] # xs) > 0" by simp

lemma nat_of_bin'_div2': "nat_of_bin' xs div 2 = nat_of_bin' (tl xs)" by (cases xs) auto
lemma nat_of_bin'_div2[simp]: "nat_of_bin' (a # xs) div 2 = nat_of_bin' xs"
  unfolding nat_of_bin_div2' by simp

lemma nat_of_bin'_max: "nat_of_bin' xs < 2 ^ (length xs)" by (induction xs) auto
lemma nat_of_bin'_min: "ends_in [True] xs \<Longrightarrow> nat_of_bin' xs \<ge> 2 ^ (length xs - 1)"
  by (auto simp: nat_of_bin_app1)


lemma bin'_of_nat_double: "n > 0 \<Longrightarrow> bin'_of_nat (2 * n) = [False] # (bin'_of_nat n)"
  apply (induction n rule: nat_induct_non_zero)
   apply (auto simp: numeral_2_eq_2 inc_inc)
  by (metis add_self_div_2 bin_of_nat_div2 list.sel(3))

corollary bin'_of_nat_double_p1: "bin'_of_nat (2 * n + 1) = [True] # (bin'_of_nat n)"
  using bin_of_nat_double by (cases "n > 0") auto


corollary nat_of_bin'_drop: "nat_of_bin' (drop k xs) = (nat_of_bin' xs) div 2 ^ k"
  (is "?n (drop k xs) = (?n xs) div 2 ^ k")
proof (induction k)
  case (Suc k)
  have "?n (drop (Suc k) xs) = ?n (tl (drop k xs))" unfolding drop_Suc drop_tl ..
  also have "... = ?n (drop k xs) div 2" unfolding nat_of_bin'_div2' ..
  also have "... = ?n xs div 2 ^ k div 2" unfolding Suc.IH ..
  also have "... = ?n xs div 2 ^ Suc k" unfolding div_mult2_eq power_Suc2 ..
  finally show ?case .
qed \<comment> \<open>case \<^term>\<open>k = 0\<close> by\<close> simp


subsection\<open>Addressing Leading Zeroes\<close>

text\<open>\<^typ>\<open>bin\<close> enables arbitrary string manipulation, but makes reasoning about
  numeric values more difficult, since leading zeroes cause non-injectivity.
  (\<^typ>\<open>num\<close> avoids this issue by defining the MSB to always be \<open>1\<close>,
  at the cost of being able to represent arbitrary strings.)
  To remedy this limitation when handling numeric values, we make use of \<^const>\<open>ends_in\<close>.\<close>

lemma inc'_end_True[simp]:
  fixes xs
  assumes "ends_in [True] xs"
  shows "ends_in [True] (inc' xs)"
  using assms
proof (induction xs)
  case (Cons a xs')
  from Cons.prems obtain ys where ysD: "a # xs' = ys @ [[True]]" ..
  then show ?case
  proof (cases ys)
    case Nil
    with ysD show ?thesis by simp
  next
    case (Cons b ys')
    with ysD have h1: "xs' = ys' @ [[True]]" by fastforce
    with Cons.IH obtain zs' where h2: "inc' xs' = zs' @ [[True]]" by auto
    then show ?thesis by (cases a) (auto simp add: h1 h2)
  qed
qed \<comment> \<open>case \<^term>\<open>xs = []\<close> by\<close> simp

lemma bin'_of_nat_gt_0_end_True[simp]: "n > 0 \<Longrightarrow> ends_in [True] (bin'_of_nat n)"
proof (induction n rule: nat_induct_non_zero)
  case (Suc n)
  from \<open>ends_in [True] (bin'_of_nat n)\<close> show ?case
    unfolding bin'_of_nat.simps
    by (metis bin'_of_bin_inv bin_of_nat.simps(2) inc'.simps inc'_end_True)
qed \<comment> \<open>case \<^term>\<open>n = 1\<close> by\<close> simp

lemma nat_of_bin'_gt_0_end_True[simp]:
  assumes eTw: "ends_in [True] w"
  shows "nat_of_bin' w > 0"
proof -
  have "(0::nat) < 2 ^ 0" by (rule less_exp)
  also have "... \<le> 2 ^ (length w - 1)" by fastforce
  also have "... \<le> nat_of_bin' w" using nat_of_bin'_min eTw .
  finally show ?thesis .
qed


subsection\<open>String Length\<close>

lemma inc'_len: "length xs \<le> length (inc' xs)"
  by (induction xs) auto

lemma nat_of_bin'_len_mono:
  assumes e: "ends_in [True] ys"
    and l: "length xs < length ys"
  shows "nat_of_bin' xs < nat_of_bin' ys"
proof -
  have "nat_of_bin' xs < 2 ^ (length xs)" by (rule nat_of_bin'_max)
  also have "... \<le> 2 ^ (length ys - 1)" using l by fastforce
  also have "... \<le> nat_of_bin' ys" using e by (rule nat_of_bin'_min)
  finally show ?thesis .
qed


subsubsection\<open>Bit-Length\<close>

text\<open>The number of bits in the binary representation.
  This does not count any leading zeroes; the bit-length of \<open>0\<close> is \<open>0\<close>.\<close>

abbreviation (input) bit'_length :: "nat \<Rightarrow> nat" where
  "bit'_length n \<equiv> length (bin'_of_nat n)"

value "bit'_length 0" \<comment> \<open>is @{value "bit'_length 0"}\<close>


lemma bit'_length_mono: "mono bit'_length"
proof (subst mono_iff_le_Suc, intro allI)
  fix n
  have "bit'_length n \<le> length (inc' (bin'_of_nat n))" using inc'_len .
  also have "... = bit'_length (Suc n)" using bin'_of_bin_inv by auto
  finally show "bit'_length n \<le> bit'_length (Suc n)" .
qed

lemma bin'_of_nat_len_gt_0[simp]: "n > 0 \<Longrightarrow> bit'_length n > 0"
proof (induction n rule: nat_induct_non_zero)
  case (Suc n)
  have "0 < length (bin'_of_nat n)" using Suc.IH .
  also have "... \<le> length (inc' (bin'_of_nat n))" by (rule inc'_len)
  also have "... = length (bin'_of_nat (Suc n))" using bin'_of_bin_inv by auto
  finally show ?case .
qed \<comment> \<open>case \<^term>\<open>n = 1\<close> by\<close> simp

lemma bit'_len_eq_0_iff[iff]: "bit'_length n = 0 \<longleftrightarrow> n = 0" using bin_of_nat_len_gt_0
proof (intro iffI)
  assume "bit'_length n = 0"
  then have "\<not> bit'_length n > 0" ..
  then have "\<not> n > 0" using bin'_of_nat_len_gt_0 by (rule contrapos_nn)
  then show "n = 0" ..
qed \<comment> \<open>direction \<open>\<longleftarrow>\<close> by\<close> simp

corollary bit'_len_gt_0_iff[iff]: "bit'_length n > 0 \<longleftrightarrow> n > 0"
  using bit'_len_eq_0_iff by simp

corollary bit'_len_double: "n > 0 \<Longrightarrow> bit'_length (2 * n) = bit'_length n + 1"
  unfolding bin'_of_nat_double by simp

lemma bit'_len_even_odd: "n > 0 \<Longrightarrow> bit'_length (2 * n) = bit'_length (2 * n + 1)"
proof -
  assume "n > 0"
  then have "bit'_length (2 * n) = length ([False] # bin'_of_nat n)"
    by (subst bin'_of_nat_double) simp_all
  also have "... = length ([True] # bin'_of_nat n)" by simp
  also have "... = bit'_length (2 * n + 1)" unfolding bin'_of_nat_double_p1 ..
  finally show ?thesis .
qed


subsection\<open>Inverses\<close>

lemma nat_bin'_nat[simp]: "nat_of_bin' (bin'_of_nat n) = n" (is "?nbn n = n")
proof (induction n)
  case (Suc n)
  have "?nbn (Suc n) = nat_of_bin' (inc' (bin'_of_nat n))"
    using bin'_of_bin_inv by auto
  also have "... = Suc (?nbn n)" using inc'_Suc by metis
  also have "... = Suc n" using Suc.IH by simp
  finally show ?case .
qed \<comment> \<open>case \<^term>\<open>n = 0\<close> by\<close> simp

corollary surj_nat_of_bin': "surj nat_of_bin'" using nat_bin'_nat by (rule surjI)

lemma bin'_nat_bin'[simp]: "ends_in [True] w \<Longrightarrow> set w \<subseteq> {[True], [False]} \<Longrightarrow>
                            bin'_of_nat (nat_of_bin' w) = w"
proof (induction w)
  let ?b = bin'_of_nat and ?n = nat_of_bin'
  case (Cons a w)
  have a_cases: "a = [True] \<or> a = [False]"
    using Cons.prems(2) by auto
  note IH = Cons.IH and prems1 = Cons.prems
  show ?case
  proof (cases w)
    case Nil
    with \<open>ends_in [True] (a # w)\<close> have "a = [True]" (* == True *) by simp
    with \<open>w = []\<close> show ?thesis by simp
  next
    case (Cons a' w')
    with prems1 have "ends_in [True] w" by (intro ends_in_Cons) blast+
    with nat_of_bin'_gt_0_end_True have "?n w > 0" .
    show ?thesis using a_cases
    proof
      assume "a = [True]"
      thus "bin'_of_nat (nat_of_bin' (a # w)) = a # w"
        using IH \<open>\<exists>ys. w = ys @ [[True]]\<close> bin'_of_nat_double_p1 prems1(2) by auto
    next
      assume "a = [False]"
      thus "bin'_of_nat (nat_of_bin' (a # w)) = a # w"
        using IH \<open>\<exists>ys. w = ys @ [[True]]\<close> bin'_of_nat_double prems1(2) by auto
    qed
  qed
qed \<comment> \<open>case \<^term>\<open>w = []\<close> by\<close> simp

corollary inj_on_nat_of_bin':
  "inj_on nat_of_bin' {w. ends_in [True] w \<and> set w \<subseteq> {[True], [False]}}"
  apply (intro inj_on_inverseI, elim CollectE)
  apply (rule bin'_nat_bin')
  by simp_all

lemma bij_nat_of_bin':
  "bij_betw nat_of_bin' {w. ends_in [True] w \<and> set w \<subseteq> {[True], [False]}} {0<..}"
  using inj_on_nat_of_bin'
proof (intro bij_betw_imageI)
  show "nat_of_bin' ` {w. ends_in [True] w \<and> set w \<subseteq> {[True], [False]}} = {0<..}"
  proof safe (* intro subset_antisym subsetI, unfold greaterThan_iff, elim imageE forw_subst CollectE exE *)
    fix w
    show "nat_of_bin' (w @ [[True]]) > 0" by (intro nat_of_bin'_gt_0_end_True) blast
  next
    fix n::nat assume "n > 0"
    show "n \<in> nat_of_bin' ` {w. ends_in [True] w \<and> set w \<subseteq> {[True], [False]}}"
    proof (intro image_eqI[where x="bin'_of_nat n"] CollectI)
      show "n = nat_of_bin' (bin'_of_nat n)" using nat_bin'_nat by auto
      show "ends_in [True] (bin'_of_nat n) \<and> set (bin'_of_nat n) \<subseteq> {[True], [False]}"
        using \<open>0 < n\<close> bin'_of_nat_gt_0_end_True by force
    qed
  qed
qed

lemma bin'_nat_bin'_drop_zs:
  fixes w :: "bool list list"
  assumes "set w \<subseteq> {[True], [False]}"
  shows "bin'_of_nat (nat_of_bin' w) = rev (dropWhile (\<lambda>b. b = [False]) (rev w))"
proof (insert assms, induction w rule: rev_induct)
  case (snoc x xs)
  have x_cases: "x = [True] \<or> x = [False]" using snoc.prems by simp
  thus ?case using snoc.prems
  proof safe
    assume a1: "set (xs @ [[True]]) \<subseteq> {[True], [False]}" and a2: "x = [True]"
    thus "bin'_of_nat (nat_of_bin' (xs @ [[True]])) = trimRight [False] (xs @ [[True]])"
      by simp
  next
    assume a3: "set (xs @ [[False]]) \<subseteq> {[True], [False]}" and a4: "x = [False]"
    thus "bin'_of_nat (nat_of_bin' (xs @ [[False]])) = trimRight [False] (xs @ [[False]])"
      apply auto
      using bin'_of_bin.simps bin'_of_nat.simps bin_of_bin'.simps nat_of_bin'.simps
        nat_of_bin_app0 snoc.IH by presburger
  qed
qed \<comment> \<open>case \<^term>\<open>w = []\<close> by\<close> simp

lemma len_bin'_nat_bin': "length (bin'_of_nat (nat_of_bin' w)) \<le> length w"
proof (induct w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case
  proof (cases a)
    case Nil
    have "length (bin'_of_nat (nat_of_bin' (a # w))) \<le>
          Suc (length (bin'_of_nat (nat_of_bin' w)))"
      apply auto
      using bin_of_nat_double_p1 apply force
      by (metis Suc_eq_plus1 bin_of_nat.simps(1) bit_len_double le0 list.size(3)
          mult_0_right not_gr0 order_refl)
    moreover have "length (a # w) = Suc (length w)" by simp
    ultimately show ?thesis using local.Cons by linarith
  next
    case (Cons a list)
    then show ?thesis
      by (metis bin'_of_nat_gt_0_end_True bit'_len_gt_0_iff length_greater_0_conv
          linorder_le_less_linear nat_bin'_nat nat_of_bin'_len_mono order_less_le)
  qed
qed

subsection\<open>Advanced Properties\<close>

lemma bin'_of_nat_div2: "bin'_of_nat (n div 2) = tl (bin'_of_nat n)"
proof (cases "n > 1")
  case False
  then have "n = 0 \<or> n = 1" by fastforce
  then show ?thesis by (elim disjE) auto
next
  case True
  define w where "w \<equiv> bin'_of_nat n"
  have "nat_of_bin' w = nat_of_bin' (bin'_of_nat n)" unfolding w_def ..
  then have wI: "nat_of_bin' w = n" using bin'_of_bin_inv by auto
  have w_tf: "set w \<subseteq> {[True], [False]}" unfolding w_def by auto

  from \<open>n > 1\<close> have "n \<ge> 2" by simp
  have "1 < length (bin'_of_nat 2)" unfolding numeral_2_eq_2 by simp
  also have "... \<le> length w" unfolding w_def using bit'_length_mono \<open>n \<ge> 2\<close> ..
  finally have "length w > 1" .

  with less_trans zero_less_one have "w \<noteq> []" by (fold length_greater_0_conv)
  with hd_Cons_tl have w_split: "hd w # tl w = w" .

  have eTw: "ends_in [True] w"
    unfolding w_def using bin'_of_nat_gt_0_end_True \<open>n > 1\<close> by simp
  then have "ends_in [True] (hd w # tl w)" unfolding w_split .

  from \<open>length w > 1\<close> have "length (tl w) > 0" unfolding length_tl less_diff_conv add_0 .
  then have "tl w \<noteq> []" unfolding length_greater_0_conv .
  with ends_in_Cons[of "hd w" "tl w"] eTw have eTtw: "ends_in [True] (tl w)"
    unfolding w_split .

  have "bin'_of_nat (n div 2) = bin'_of_nat (nat_of_bin' w div 2)" unfolding wI ..
  also have "... = bin'_of_nat (nat_of_bin' (tl w))" using nat_of_bin'_div2' by simp
  also have "... = tl w" using bin'_nat_bin' eTtw w_tf
    by (metis insert_subset list.simps(15) w_split)
  finally show ?thesis unfolding w_def .
qed

corollary bin'_of_nat_div2_times2: "n > 1 \<Longrightarrow>
  bin'_of_nat (2 * (n div 2)) = [False] # tl (bin'_of_nat n)"
  using bin'_of_nat_div2 bin'_of_nat_double by simp

corollary bin'_of_nat_div2_times2_len: "n > 1 \<Longrightarrow>
  bit'_length (2 * (n div 2)) = bit'_length n"
proof -
  assume "n > 1"
  then have l: "bin'_of_nat n \<noteq> []" using bin_of_nat_len_gt_0 by simp

  have "length (bin'_of_nat (2 * (n div 2))) = length ([False] # tl (bin'_of_nat n))"
    using bin'_of_nat_div2_times2 \<open>n > 1\<close> by presburger
  also have "... = length (bin'_of_nat n)" using len_tl_Cons l .
  finally show ?thesis .
qed

lemma bin'_of_nat_app_0s:
  assumes "n > 0"
  shows "bin'_of_nat (n * 2^k) = [False] \<up> k @ bin'_of_nat n"
    (is "?lhs = ?zs @ ?n")
proof -
  from \<open>n > 0\<close> have "?n \<noteq> []" using bin_of_nat_len_gt_0 by simp
  moreover from \<open>n > 0\<close> have "ends_in [True] ?n" by (rule bin'_of_nat_gt_0_end_True)
  ultimately have eTr: "ends_in [True] (?zs @ ?n)" unfolding ends_in_append by simp

  have "?lhs = bin'_of_nat (nat_of_bin' ?n * 2^k)" using nat_bin'_nat by auto
  also have "... = bin'_of_nat (nat_of_bin' (?zs @ ?n))" using nat_of_bin_app_0s by simp
  also have "... = ?zs @ ?n" using eTr assms bin_of_nat_app_0s nat_bin'_nat
      nat_of_bin_app_0s by auto
  finally show ?thesis .
qed

lemma nat_of_bin'_app_1s: "nat_of_bin' ([True] \<up> n @ xs) = nat_of_bin' xs * 2^n + 2^n - 1"
proof (induction n)
  case (Suc n)

  have h1: "c \<ge> a \<Longrightarrow> a \<ge> b \<Longrightarrow> c - a + b = c - (a - b)" for a b c ::nat by simp
  have h2: "nat_of_bin' xs * 2^(Suc n) + 2^(Suc n) \<ge> 2" by (intro trans_le_add2) simp
  note h3 = h2[THEN h1]

  have "nat_of_bin' ([True] \<up> (Suc n) @ xs) = nat_of_bin' ([True] # [True] \<up> n  @ xs)"
    by simp
  also have "\<dots> = 2 * (nat_of_bin' xs * 2^n + 2^n - 1) + 1" using Suc.IH by simp
  also have "\<dots> = 2 * (nat_of_bin' xs * 2^n + 2^n) - 2 + 1"
    unfolding diff_mult_distrib2 by simp
  also have "\<dots> = nat_of_bin' xs * 2 * 2^n + 2 * 2^n - 2 + 1"
    unfolding add_mult_distrib2 mult.assoc[symmetric] by (simp add: mult.commute)
  also have "\<dots> = nat_of_bin' xs * 2^(Suc n) + 2^(Suc n) - 2 + 1"
    unfolding power_Suc mult.assoc ..
  also have "\<dots> = nat_of_bin' xs * 2^(Suc n) + 2^(Suc n) - 1" by (subst h3) simp_all
  finally show ?case .
qed \<comment> \<open>case \<^term>\<open>n = 0\<close> by\<close> simp

lemma bin'_of_nat_end_True[iff]: "ends_in [True] (bin'_of_nat n) \<longleftrightarrow> n > 0"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (intro iffI)
  show "?lhs \<Longrightarrow> ?rhs" by (drule nat_of_bin'_gt_0_end_True) (unfold nat_bin'_nat)
  show "?rhs \<Longrightarrow> ?lhs" by (rule bin'_of_nat_gt_0_end_True)
qed


lemma take_mod': "((nat_of_bin' w) mod 2^k) = nat_of_bin' (take k w)"
proof (induction w arbitrary: k)
  case (Cons a w)
  show ?case proof (cases "k > 0")
    case True
    then have "k = k - 1 + 1" by force

    have "(2 * (nat_of_bin' w)) mod 2 ^ k = (2 * (nat_of_bin' w)) mod 2 ^ (k - 1 + 1)"
      by (subst \<open>k = k - 1 + 1\<close>) (rule refl)
    also have "... = (2 * (nat_of_bin' w)) mod (2 * 2^(k-1))" by force
    also have "... = 2 * ((nat_of_bin' w) mod 2 ^ (k-1))"
      by (rule mult_mod_right[symmetric])
    also have "... = 2 * (nat_of_bin' (take (k - 1) w))"
      unfolding \<open>(nat_of_bin' w) mod 2 ^ (k-1) = (nat_of_bin' (take (k-1) w))\<close> ..
    finally have *: "(2 * (nat_of_bin' w)) mod 2 ^ k = 2 * (nat_of_bin' (take (k - 1) w))" .

    show ?thesis proof (induction a)
      case Nil
      then show ?case apply auto
         apply (metis (full_types) list.simps(9) nat_of_bin.simps(2) plus_1_eq_Suc
            take_map take_mod)
        by (metis (full_types) Cons_eq_map_conv add_0 nat_of_bin.simps(2)
            take_map take_mod)
    next
      case (Cons a1 a2)
      then show ?case apply auto
         apply (metis (full_types) list.sel(1) list.simps(9) nat_of_bin.simps(2)
            plus_1_eq_Suc take_map take_mod)
        by (metis (full_types) add_0 list.sel(1) list.simps(9) nat_of_bin.simps(2)
            take_map take_mod)
    qed
  qed \<comment> \<open>case \<^term>\<open>k = 0\<close> by\<close> simp
qed \<comment> \<open>case \<^term>\<open>w = []\<close> by\<close> simp


subsection\<open>Log and Bit-Length\<close>

lemma bit'_len_eq_log2: "n > 0 \<Longrightarrow> bit'_length n = nat_log 2 n + 1"
proof (induction n rule: log2_induct)
  case (div n)
  from \<open>n \<ge> 2\<close> have "n div 2 > 0" by force

  have "bit'_length n = bit'_length (2 * (n div 2))" using \<open>n \<ge> 2\<close>
    by (subst bin'_of_nat_div2_times2_len) force+
  also have "... = bit'_length (n div 2) + 1"
    using \<open>n \<ge> 2\<close> by (subst bit'_len_double) force+
  also have "... = nat_log 2 (n div 2) + 1 + 1" unfolding div.IH ..
  also have "... = nat_log 2 (n) + 1" using log2.rec[OF \<open>n \<ge> 2\<close>] by presburger
  finally show "bit'_length n = nat_log 2 n + 1" .
qed \<comment> \<open>case \<^term>\<open>n < 2\<close> by\<close> force+

lemma bit'_length_eq_log:
  assumes "n > 0"
  shows "bit'_length n = \<lfloor>log 2 n\<rfloor> + 1"
  using assms log2.altdef bit_len_eq_log2 by auto


subsection\<open>Order\<close>

text\<open>From @{cite \<open>ch.~4.4\<close> rassOwf2017}: "we will order two words \<open>u, v \<in> \<Sigma>\<^sup>*\<close> as \<open>u \<le> v \<Longleftrightarrow> (u)\<^sub>2 \<le> (v)\<^sub>2\<close>."
  Note: defining the \<^const>\<open>less\<close> relation is necessary for \<^class>\<open>ord\<close>
  (of which \<^class>\<open>preorder\<close> is a subclass).
  As anti-symmetry is not given, no partial order (\<^class>\<open>order\<close>) can be established.\<close>

\<comment> \<open>The following approach (locale interpretation instead of class instantiation)
  is necessary as \<^typ>\<open>bin\<close> is defined as a type-synonym and not as independent type.\<close>
interpretation bin'_preorder:
  preorder "\<lambda>a b. (nat_of_bin' a) \<le> (nat_of_bin' b)"
           "\<lambda>a b. (nat_of_bin' a) < (nat_of_bin' b)"
  using less_le_not_le le_refl le_trans apply simp apply (rule class.preorder.intro)
  by auto


subsection\<open>Number of Binary Strings of Given Length\<close>

lemma card_bin'_len_eq:
  "card {w::bin'. length w = l \<and> set w \<subseteq> {[True], [False]}} = 2 ^ l"
proof -
  let ?bools = "{[True], [False]}"
  have card_bools: "card ?bools = 2" by simp
  have "card {w::bin'. length w = l \<and> set w \<subseteq> {[True], [False]}} =
        card {w. set w \<subseteq> ?bools \<and> length w = l}" by metis
  also have "... = card ?bools ^ l" by (intro card_lists_length_eq) simp
  also have "... = 2 ^ l" unfolding card_bools ..
  finally show ?thesis .
qed

corollary finite_bin'_len_eq:
  "finite {w::bin'. length w = l \<and> set w \<subseteq> {[True], [False]}}"
  using card_bin'_len_eq by (intro card_ge_0_finite) presburger

corollary finite_bin'_len_less:
  "finite {w::bin'. length w < l \<and> set w \<subseteq> {[True], [False]}}"
proof -
  let ?W = "\<lambda>l. {w::bin'. length w = l \<and> set w \<subseteq> {[True], [False]}}"
  let ?W\<^sub>L = "{?W l' | l'. l' < l}"

  have *: "{w::bin'. length w < l \<and> set w \<subseteq> {[True], [False]}} = \<Union> ?W\<^sub>L" by blast
  show "finite {w::bin'. length w < l \<and> set w \<subseteq> {[True], [False]}}" unfolding *
    using finite_bin_len_eq apply (intro finite_Union) apply auto
    by (rule finite_bin'_len_eq)
qed

lemma card_bin'_len_less:
  "card {w::bin'. length w < l \<and> set w \<subseteq> {[True], [False]}} = 2 ^ l - 1"
proof -
  let ?W = "\<lambda>l. {w::bin'. length w = l \<and> set w \<subseteq> {[True], [False]}}"
  let ?W\<^sub>L = "{?W l' | l'. l' < l}"

  have "card {w::bin'. length w < l \<and> set w \<subseteq> {[True], [False]}} = card (\<Union> ?W\<^sub>L)"
    by (intro arg_cong[where f=card]) blast
  also have "card (\<Union> ?W\<^sub>L) = sum card ?W\<^sub>L"
  proof (intro card_Union_disjoint)
    show "pairwise disjnt ?W\<^sub>L"
    proof (intro pairwiseI)
      fix x y
      assume "x \<in> ?W\<^sub>L" then obtain l\<^sub>x where l\<^sub>x: "x = ?W l\<^sub>x" by blast
      assume "y \<in> ?W\<^sub>L" then obtain l\<^sub>y where l\<^sub>y: "y = ?W l\<^sub>y" by blast

      assume "x \<noteq> y"
      then have "l\<^sub>x \<noteq> l\<^sub>y" unfolding l\<^sub>x l\<^sub>y by force
      then show "disjnt x y" unfolding l\<^sub>x l\<^sub>y disjnt_def by blast
    qed

    fix W
    assume "W \<in> ?W\<^sub>L" then obtain l\<^sub>W where "W = ?W l\<^sub>W" by blast
    show "finite W" unfolding \<open>W = ?W l\<^sub>W\<close> by (rule finite_bin'_len_eq)
  qed
  also have "sum card ?W\<^sub>L = sum card (?W ` {..<l})"
    by (intro arg_cong[where f="sum card"]) (unfold lessThan_def, rule image_Collect[symmetric])
  also have "sum card (?W ` {..<l}) = sum (card \<circ> ?W) {..<l}"
  proof (intro sum.reindex inj_onI)
    fix x y :: nat
    obtain w :: bin' where "length w = x" and "set w \<subseteq> {[True], [False]}"
      by (meson length_replicate set_replicate_subset subset_insertI2)
    assume "?W x = ?W y"
    then have "w \<in> ?W x \<longleftrightarrow> w \<in> ?W y" by (rule arg_cong)
    hence "length w = x \<and> set w \<subseteq> {[True], [False]} \<longleftrightarrow>
           length w = y \<and> set w \<subseteq> {[True], [False]}" by simp
    hence "length w = x \<Longrightarrow> length w = y"
      by (simp add: \<open>set w \<subseteq> {[True], [False]}\<close>)
    then show "x = y" unfolding \<open>length w = x\<close> by force
  qed
  also have "sum (card \<circ> ?W) {..<l} = (\<Sum>n<l. 2^n)"
    unfolding comp_def card_bin'_len_eq ..
  also have "... = 2^l - 1" unfolding lessThan_atLeast0 by (rule sum_power2)
  finally show ?thesis .
qed

lemma drop_True_False: "set w \<subseteq> {[True], [False]} \<Longrightarrow>
                        set (drop k w) \<subseteq> {[True], [False]}"
proof (induct w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case by (meson dual_order.trans set_drop_subset)
qed

lemma bit'_length_pow2_eq: "bit'_length n = k \<Longrightarrow> n < 2 ^ k"
proof (induct k)
  case 0
  then show ?case by fastforce
next
  case (Suc k)
  then show ?case by (metis nat_bin'_nat nat_of_bin'_max)
qed

lemma lengths_le: "n \<le> x \<Longrightarrow> length (bin_of_nat n) \<le> length (bin_of_nat x)"
  apply (induction x)
   apply (induction n)
    apply auto
  by (metis inc_Suc inc_len le_Suc_eq le_trans len_bin_nat_bin nat_bin_nat)

lemma lengths_lt: "length (bin_of_nat n) < length (bin_of_nat x) \<Longrightarrow> n < x"
  apply (induction x)
   apply (induction n)
    apply auto
  by (metis bin_of_nat.simps(2) lengths_le verit_comp_simplify1(3))

lemma lengths_bin_bin'_eq: "length (bin_of_nat n) = length (bin'_of_nat n)"
  by simp
end
