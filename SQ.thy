chapter\<open>A Hard Language with a Known Density Bound\<close>

section\<open>The Language of Integer Squares\<close>

theory SQ
  imports Language_Density
    "Supplementary/Discrete_Log" "Supplementary/Discrete_Sqrt" "Supplementary/Sublists"
    "Intro_Dest_Elim.IHOL_IDE"
begin


text\<open>SQ is an overloaded identifier in @{cite rassOwf2017}.
  However, the more common notion is the language as opposed to the set of natural numbers.\<close>

definition SQ :: "bool lang" \<comment> \<open>The language of non-zero square numbers, represented by binary strings without leading ones.\<close>
  where "SQ \<equiv> Lang UNIV (\<lambda>w. \<exists>x. gn w = x\<^sup>2)"

definition SQ_nat :: "nat set" \<comment> \<open>The analogous set \<open>SQ \<subseteq> \<nat>\<close>, as defined in @{cite \<open>ch.~4.1\<close> rassOwf2017}.\<close>
  where [simp]: "SQ_nat \<equiv> {y. y \<noteq> 0 \<and> (\<exists>x. y = x\<^sup>2)}"


lemma member_SQ[simp]: "w \<in>\<^sub>L SQ \<longleftrightarrow> (\<exists>x. gn w = x\<^sup>2)" by (simp add: SQ_def)

lemma SQ_nat_zero:
	"insert 0 SQ_nat = {y. \<exists>x. y = x ^ 2}"
	"SQ_nat = {y. \<exists>x. y = x ^ 2} - {0}"
	by auto

text\<open>Relating \<^const>\<open>SQ\<close> and \<^const>\<open>SQ_nat\<close>:\<close>
lemma SQ_SQ_nat_eq: "words SQ = {w. gn w \<in> SQ_nat}" by auto

lemma SQ_nat_im: "SQ_nat = gn ` words SQ"
proof (intro subset_antisym subsetI image_eqI CollectI)
  fix n assume "n \<in> SQ_nat"
  then have "n > 0" by simp
  then show "n = gn (gn_inv n)" by simp

  from \<open>n \<in> SQ_nat\<close> have "\<exists>x. n = x ^ 2" by simp
  then obtain x where b: "n = x ^ 2" ..
  with \<open>n > 0\<close> show "gn_inv n \<in>\<^sub>L SQ" by simp
next
  fix n
  assume "n \<in> gn ` words SQ"
  then have "n > 0" using gn_gt_0 by blast
  from \<open>n \<in> gn ` words SQ\<close> have "n \<in> {n. \<exists>x. gn (gn_inv n) = x ^ 2}" using gn_inv_id by fastforce
  then have "\<exists>x. gn (gn_inv n) = x ^ 2" by blast
  then obtain x where "gn (gn_inv n) = x ^ 2" ..
  with \<open>n > 0\<close> have "n = x ^ 2" using inv_gn_id by simp
  with \<open>n > 0\<close> show "n \<in> SQ_nat" by simp
qed


text\<open>``Lemma 4.2 @{cite rassOwf2017}. The language of squares \<open>SQ = {y. y = x\<^sup>2 \<and> x \<in> \<nat>}\<close>
  has a density function \<open>dens\<^sub>S\<^sub>Q(x) \<in> \<Theta>(\<surd>x)\<close>.''\<close>

theorem dens_SQ: "dens SQ x = dsqrt x"
proof -
  have eq: "{w\<in> words SQ. gn w \<le> x} = gn_inv ` power2 ` {0<..dsqrt x}"
  proof (intro subset_antisym subsetI image_eqI CollectI conjI)
    fix w
    assume "w \<in> {w \<in> words SQ. gn w \<le> x}"
    then have "w \<in>\<^sub>L SQ" and "gn w \<le> x" by blast+

    show "w = gn_inv (gn w)" unfolding gn_inv_id ..

    from \<open>w \<in>\<^sub>L SQ\<close> obtain z where "gn w = z\<^sup>2" unfolding SQ_def by auto
    then have "z = dsqrt (gn w)" by simp
    then show "gn w = (dsqrt (gn w))\<^sup>2" using \<open>gn w = z\<^sup>2\<close> by blast

    from \<open>gn w \<le> x\<close> have "dsqrt (gn w) \<le> dsqrt x" by (rule mono_sqrt')
    moreover have "dsqrt (gn w) > 0" using gn_gt_0 by simp
    ultimately show "dsqrt (gn w) \<in> {0<..dsqrt x}" by simp
  next
    fix w
    assume "w \<in> gn_inv ` power2 ` {0<..dsqrt x}"
    then obtain z where zw: "w = gn_inv (z\<^sup>2)" and zx: "z \<in> {0<..dsqrt x}" by blast
    from zx have "z > 0" and "z \<le> dsqrt x" unfolding greaterThanAtMost_iff by blast+

    from zw have "gn w = gn (gn_inv (z\<^sup>2))" by blast
    also have "... = z\<^sup>2" using inv_gn_id zero_less_power \<open>z > 0\<close> .
    finally have "gn w = z\<^sup>2" .
    then show "w \<in>\<^sub>L SQ" unfolding SQ_def by simp
    from \<open>gn w = z\<^sup>2\<close> and \<open>z \<le> dsqrt x\<close> show "gn w \<le> x" using le_sqrt_iff by simp
  qed

  have "power2 ` {0<..dsqrt x} \<subseteq> {0<..}" by auto
  with inj_on_subset gn_inv_inj have "inj_on gn_inv (power2 ` {0<..dsqrt x})" .
  with card_image have "dens SQ x = card (power2 ` {0<..dsqrt x})" unfolding dens_def eq .
  also have "\<dots> = card {0<..dsqrt x}" by (intro card_image, unfold inj_on_def) fastforce
  also have "\<dots> = dsqrt x" by simp
  finally show ?thesis .
qed


subsection\<open>Log Inequality\<close>

lemma nat_pow_nat:
  fixes b :: nat and x :: int
  assumes "x \<ge> 0" "b > 0"
  shows "(b powr x) \<in> \<nat>"
proof -
  from assms have "b powr x = b ^ (nat x)" using powr_real_of_int by simp
  moreover have "real (b ^ (nat x)) \<in> \<nat>" using of_nat_in_Nats by blast
  ultimately show ?thesis by simp
qed

lemma nat_eq_ceil_floor:
  fixes n :: real
  assumes "n \<in> \<nat>"
  shows nat_eq_ceil: "\<lceil>n\<rceil> = n"
    and nat_eq_floor: "\<lfloor>n\<rfloor> = n"
  using assms
  by (cases n rule: Nats_cases; simp)+

lemma log_ceil_le:
  assumes "x \<ge> 1"
  shows "log 2 \<lceil>x\<rceil> \<le> \<lceil>log 2 x\<rceil>"
proof -
  from \<open>x \<ge> 1\<close> have "x = 2 powr (log 2 x)" using powr_log_cancel[of 2 x] by simp
  also have "2 powr (log 2 x) \<le> 2 powr \<lceil>log 2 x\<rceil>" by simp
  finally have "x \<le> 2 powr \<lceil>log 2 x\<rceil>" .

  then have *: "\<lceil>x\<rceil> \<le> \<lceil>2 powr \<lceil>log 2 x\<rceil>\<rceil>" by (rule ceiling_mono)
  have "\<lceil>x\<rceil> \<le> 2 powr \<lceil>log 2 x\<rceil>"
  proof -
    from \<open>x \<ge> 1\<close> have "log 2 x \<ge> 0" by simp
    then have "\<lceil>log 2 x\<rceil> \<ge> 0" by simp
    then have "2 powr \<lceil>log 2 x\<rceil> \<in> \<nat>" using nat_pow_nat[of "\<lceil>log 2 x\<rceil>" 2] by simp
    then have "\<lceil>2 powr \<lceil>log 2 x\<rceil>\<rceil> = 2 powr \<lceil>log 2 x\<rceil>" using nat_eq_ceil by simp
    with * show ?thesis by auto
  qed
  thus "log 2 \<lceil>x\<rceil> \<le> \<lceil>log 2 x\<rceil>" using Transcendental.log_le_iff assms by simp
qed

lemma log2_sqrt:
  fixes x :: real
  assumes "x > 0"
  shows "log 2 (sqrt x) = (log 2 x) / real 2"
  unfolding sqrt_def using pos2 \<open>x > 0\<close> by (rule log_root)

corollary log2_sqrt':
  fixes x :: real
  assumes "x > 0"
  shows "log 2 (sqrt x) = (log 2 x) / 2"
  using log2_sqrt and \<open>x > 0\<close> by simp

lemma log_eq_cancel_iff:
  assumes "a > 1" "x > 0" "y > 0"
  shows "(log a x = log a y) = (x = y)"
proof (intro iffI)
  assume l_eq: "log a x = log a y"
  then have "log a x \<le> log a y" and "log a x \<ge> log a y" by simp_all
  with assms have "x \<le> y" and "x \<ge> y" by simp_all
  then show "x = y" by simp
qed (rule arg_cong)

lemma floor_eq_ceil_nat: "\<lfloor>x\<rfloor> = \<lceil>x\<rceil> \<longleftrightarrow> x = of_int \<lfloor>x\<rfloor>" unfolding ceiling_altdef by simp
lemma ceil_le_floor_plus1: "\<lceil>x\<rceil> \<le> \<lfloor>x\<rfloor> + 1" unfolding ceiling_altdef by simp

lemma ceil_le_floor_plus1_nat: "nat \<lceil>x\<rceil> \<le> nat \<lfloor>x\<rfloor> + 1"
proof (cases "x > 0")
  assume "x > 0"
  then have "\<lfloor>x\<rfloor> \<ge> 0" unfolding zero_le_floor by (rule less_imp_le)
  then have int_nat_x: "int (nat \<lfloor>x\<rfloor>) = \<lfloor>x\<rfloor>" by (rule nat_0_le)

  from ceil_le_floor_plus1 have "nat \<lceil>x\<rceil> \<le> nat (\<lfloor>x\<rfloor> + 1)" by (rule nat_mono)
  also have "nat (\<lfloor>x\<rfloor> + 1) = nat (int (nat \<lfloor>x\<rfloor>) + int 1)" unfolding int_nat_x of_nat_1 ..
  also have "... = nat \<lfloor>x\<rfloor> + 1" using nat_int_add .
  finally show "nat \<lceil>x\<rceil> \<le> nat \<lfloor>x\<rfloor> + 1" .
qed \<comment> \<open>case \<open>x \<le> 0\<close> by\<close> simp


subsection\<open>Length of Prefix\<close>

text\<open>\<open>w'\<close> (\<^term>\<open>next_square n\<close>) will eventually have an identical lot of \<open>\<lceil>log l\<rceil>\<close> most significant bits.\<close>

(* TODO format the following note as text *)
(*
 * but what about when the carry "wraps over", for instance n := 31
 *
 * 25 : 011001  <- prev_square n
 * 26 : 011010
 * 27 : 011011
 * 28 : 011100
 * 29 : 011101
 * 30 : 011110
 * 31 : 011111  <- n
 * 32 : 100000
 * 33 : 100001
 * 34 : 100010
 * 35 : 100011
 * 36 : 100100  <- next_square n
 *
 * no shared prefix.
 * our fix: define adj_square n as the next_square of the preceding power-of-2
 *)

lemma adj_sq_diff_pow2: "2 * dsqrt n + 1 < 2 ^ (4 + bit_length n div 2)"
proof (cases "n > 0")
  assume "n > 0"
  then have n0r: "n > (0::real)"
    and s1: "sqrt n \<ge> 1"
    and ds0: "\<lfloor>sqrt n\<rfloor> > 0"
    by simp_all

  have "1 < (2::real)" by simp
  note log_mono = \<open>1 < 2\<close>[THEN log_le_cancel_iff]
    and log_mono_strict = \<open>1 < 2\<close>[THEN log_less_cancel_iff]

  have "log 2 (2 * \<lfloor>sqrt n\<rfloor> + 1) \<le> log 2 (2 * sqrt n + 1)"
  proof -
    have "2 * \<lfloor>sqrt n\<rfloor> + 1 \<le> 2 * sqrt n + 1" by simp
    moreover have "2 * \<lfloor>sqrt n\<rfloor> + 1 > (0::real)" "2 * sqrt n + 1 > 0" using s1 by linarith+
    ultimately show ?thesis using log_mono by blast
  qed
  also have "... < log 2 (4 * sqrt n)"
  proof -
    have "a \<ge> 1 \<Longrightarrow> 2 * a + 1 < 4 * a" for a :: real by simp
    then have "2 * sqrt n + 1 < 4 * sqrt n" using s1 .
    moreover from s1 have "2 * sqrt n + 1 > 0" and "4 * sqrt n > 0" by linarith+
    ultimately show ?thesis using log_mono_strict by blast
  qed
  also have "... = log 2 (2 powr 2 * sqrt n)" by simp
  also have "... = 2 + log 2 (sqrt n)" using \<open>n > 0\<close> add_log_eq_powr by simp
  also have "... = 2 + log 2 n / 2" unfolding n0r[THEN log2_sqrt'] ..
  finally have *: "log 2 (2 * \<lfloor>sqrt n\<rfloor> + 1) < 2 + log 2 n / 2" .

  have "real (2 * dsqrt n + 1) = 2 * \<lfloor>sqrt n\<rfloor> + 1" unfolding sqrt_altdef_nat by simp
  also have "... = 2 powr (log 2 (2 * \<lfloor>sqrt n\<rfloor> + 1))" using ds0 powr_log_cancel
  proof -
    from ds0 have "real_of_int (2 * \<lfloor>sqrt n\<rfloor> + 1) > 0" by linarith
    with powr_log_cancel show ?thesis by simp
  qed
  also have "... < 2 powr (2 + log 2 n / 2)" using * by simp
  also have "... \<le> 2 powr (4 + nat_log 2 n div 2)"
  proof -
    have "2 + log 2 (real n) / 2 \<le> 4 + \<lfloor>\<lfloor>log 2 (real n)\<rfloor> / 2\<rfloor>" by linarith
    also have "... = 4 + \<lfloor>log 2 (real n)\<rfloor> div 2"
      unfolding floor_divide_of_int_eq[of _ 2, unfolded of_int_numeral] ..
    also have "... = 4 + nat_log 2 n div 2"
    proof -
      from \<open>n > 0\<close> have "n \<noteq> 0" ..
      with log2.altdef have *: "\<lfloor>log 2 n\<rfloor> = int (nat_log 2 n)" by simp
      then have "4 + \<lfloor>log 2 (real n)\<rfloor> div 2 = (4 + (int (nat_log 2 n)) div 2)" unfolding * by blast
      also have "... = 4 + nat_log 2 n div 2" unfolding of_nat_add of_nat_numeral of_nat_div ..
      finally have **: "4 + \<lfloor>log 2 n\<rfloor> div 2 = 4 + nat_log 2 n div 2" .
      show ?thesis unfolding ** using of_int_of_nat_eq .
    qed
    finally show ?thesis by simp
  qed
  also have "... = 2 ^ (4 + nat_log 2 n div 2)" by (intro powr_realpow[of 2]) simp
  finally have "real (2 * dsqrt n + 1) < real (2 ^ (4 + nat_log 2 n div 2))" by simp
  then have "2 * dsqrt n + 1 < 2 ^ (4 + nat_log 2 n div 2)" unfolding of_nat_less_iff .

  also have "... \<le> 2 ^ (4 + bit_length n div 2)" using \<open>n > 0\<close> by (subst bit_len_eq_log2) auto
  finally show ?thesis .
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp

lemma adj_sq_diff: "next_square n - prev_square n < 2 ^ (4 + bit_length n div 2)"
  using adj_sq_diff_pow2 next_prev_sq_diff by (rule dual_order.strict_trans2)

lemma next_sq_diff: "next_square n - n < 2 ^ (4 + bit_length n div 2)"
  using adj_sq_diff_pow2 next_sq_diff by (rule dual_order.strict_trans2)


subsection\<open>Adjacent Square\<close>

definition suffix_len :: "bin \<Rightarrow> nat"
  where "suffix_len w \<equiv> 5 + length w div 2"

lemma suffix_min_len: "length w \<ge> 9 \<Longrightarrow> suffix_len w \<le> length w" unfolding suffix_len_def by linarith

(*
 * Choose the adjacent square of \<open>n\<close> as the \<open>next_square\<close> of the smallest number sharing its prefix.
 * That is, the prefix concatenated with zeroes to have the same length as \<open>n\<close>.
 *)
definition adj_square :: "nat \<Rightarrow> nat"
  where "adj_square n = next_square (n - n mod 2^(suffix_len (gn_inv n)))"

lemma adj_sq_gt_0: "adj_square n > 0" unfolding adj_square_def by (rule next_sq_gt0)

lemma adj_sq_correct: "is_square (adj_square n)"
  unfolding adj_square_def using next_sq_correct1 .

lemma adj_sq_correct': "gn_inv (adj_square n) \<in>\<^sub>L SQ"
  using adj_sq_gt_0 adj_sq_correct by simp


definition adj_sq\<^sub>w :: "word \<Rightarrow> word"
  where [simp]: "adj_sq\<^sub>w w \<equiv> gn_inv (adj_square (gn w))"

theorem adj_sq_word_correct: "adj_sq\<^sub>w w \<in>\<^sub>L SQ" unfolding adj_sq\<^sub>w_def
  using adj_sq_correct and adj_sq_gt_0 by simp


subsection\<open>Shared Prefix\<close>

definition shared_MSBs :: "nat \<Rightarrow> bin \<Rightarrow> bin \<Rightarrow> bool"
  where "shared_MSBs l a b \<equiv> length b = length a \<and> drop (length b - l) b = drop (length a - l) a"


mk_ide shared_MSBs_def |intro sh_msbI[intro]| |dest sh_msbD[dest]|

lemma sh_msbD'[dest]:
  assumes "shared_MSBs l a b"
  shows "drop (length a - l) b = drop (length a - l) a"
proof -
  from assms have *: "length b = length a" ..
  from assms have "drop (length b - l) b = drop (length a - l) a" ..
  then show ?thesis unfolding * .
qed

lemma sh_msb_le:
  assumes "L \<ge> l"
    and shL: "shared_MSBs L a b"
  shows "shared_MSBs l a b"
proof -
  from shL have l_ab: "length b = length a" ..

  from \<open>L \<ge> l\<close> have "length a - L \<le> length a - l" by (rule diff_le_mono2)
  moreover from shL have "drop (length a - L) b = drop (length a - L) a" ..
  ultimately have "drop (length b - l) b = drop (length a - l) a" unfolding l_ab by (rule drop_eq_le)

  with l_ab show "shared_MSBs l a b" ..
qed

lemma sh_msb_comm: "shared_MSBs l a b \<Longrightarrow> shared_MSBs l b a" unfolding shared_MSBs_def by argo

lemma bit_len_le_pow2: "n < 2 ^ k \<Longrightarrow> bit_length n \<le> k"
proof (cases "n > 0", cases "k > 0")
  assume "n > 0" and "k > 0" and "n < 2 ^ k"
  from \<open>n > 0\<close> \<open>n < 2 ^ k\<close> have "n \<le> 2 ^ k - 1" by linarith

  from \<open>n > 0\<close> have "bit_length n = nat_log 2 n + 1" by (rule bit_len_eq_log2)
  also have "... \<le> nat_log 2 (2 ^ k - 1) + 1" unfolding add_le_cancel_right
    using \<open>n \<le> 2 ^ k - 1\<close> by (rule nat_log_le_iff)
  also have "... = k" unfolding log2.exp_m1 using \<open>k > 0\<close> by simp
  finally show ?thesis .
qed \<comment> \<open>cases \<open>n = 0\<close> and \<open>k = 0\<close> by\<close> fastforce+

(* suppl *)
lemma pow2_min: "0 < n \<Longrightarrow> n < 2^k \<Longrightarrow> k > 0" for n k :: nat by (cases "k > 0") force+

lemma add_suffix_bin:
  fixes up lo k :: nat
  assumes "lo < 2^k"
  shows "up * 2^k + lo = ((bin_of_nat lo) @ (False \<up> (k - (bit_length lo))) @ (bin_of_nat up))\<^sub>2"
    (is "?lhs = (?lo @ ?zs @ ?up)\<^sub>2")
proof (cases "up > 0", cases "lo > 0")
  assume "up > 0" and "lo > 0"
  let ?n = nat_of_bin
    and ?b = bin_of_nat
    and ?z = "\<lambda>l. False \<up> l"

  have "k > 0" using \<open>lo > 0\<close> \<open>lo < 2^k\<close> by (rule pow2_min)
  have "bit_length lo \<le> k" using \<open>lo < 2^k\<close> by (rule bit_len_le_pow2)
  with le_add_diff_inverse have lloz: "length (?lo @ ?zs) = k"
    unfolding length_append length_replicate .

  have "?n (?lo @ ?zs @ ?up) = ?n ((?lo @ ?zs) @ ?up)" unfolding append_assoc ..
  also have "... = up * 2 ^ length (?lo @ ?zs) + lo" unfolding nat_of_bin_app by simp
  also have "... = ?lhs" unfolding lloz ..
  finally show ?thesis by (rule sym)
qed \<comment> \<open>cases \<open>up = 0\<close> and \<open>lo = 0\<close> by\<close> (simp_all add: nat_of_bin_app_0s)

corollary add_suffix_bin':
  fixes up lo k :: nat
  assumes "up > 0" \<comment> \<open>required to prevent leading zeroes\<close>
    and "lo < 2^k"
  shows "bin_of_nat (up * 2^k + lo) = (bin_of_nat lo) @ (False \<up> (k - (length (bin_of_nat lo)))) @ (bin_of_nat up)"
    (is "?lhs = ?lo @ ?zs @ ?up")
proof -
  from \<open>up > 0\<close> have "ends_in True ?up" unfolding bin_of_nat_end_True .
  moreover from bin_of_nat_len_gt_0 and \<open>up > 0\<close> have "?up \<noteq> []" unfolding length_greater_0_conv .
  ultimately have "ends_in True (?lo @ ?zs @ ?up)" unfolding ends_in_append by force

  with bin_nat_bin[symmetric] have "?lo @ ?zs @ ?up = bin_of_nat (nat_of_bin (?lo @ ?zs @ ?up))" .
  also have "... = ?lhs" using add_suffix_bin[of lo k up] assms by presburger
  finally show ?thesis by (rule sym)
qed


lemma drop_suffix_bin:
  fixes lo up :: bin and k :: nat
  assumes "ends_in True up" and lo: "(lo)\<^sub>2 < 2 ^ k"
  shows "drop k (bin_of_nat ((up)\<^sub>2 * 2^k + (lo)\<^sub>2)) = up" (is "drop k ?lhs = up")
proof -
  from \<open>ends_in True up\<close> have up: "(up)\<^sub>2 > 0" by (rule nat_of_bin_gt_0_end_True)
  from \<open>(lo)\<^sub>2 < 2 ^ k\<close> have "bit_length (lo)\<^sub>2 \<le> k" by (rule bit_len_le_pow2)
  then have drop_k_lo: "drop k (bin_of_nat (lo)\<^sub>2) = []" by (rule drop_all)

  let ?lo = "bin_of_nat (lo)\<^sub>2"
  let ?loz = "?lo @ False \<up> (k - length ?lo)"

  have lo_simps: "length ?loz = k" "drop k ?lo = []" using \<open>bit_length (lo)\<^sub>2 \<le> k\<close> by force+
  have split: "?lhs = ?loz @ bin_of_nat (up)\<^sub>2" unfolding append.assoc
    using \<open>(up)\<^sub>2 > 0\<close> \<open>(lo)\<^sub>2 < 2 ^ k\<close> by (rule add_suffix_bin')

  have "drop k ?lhs = bin_of_nat (up)\<^sub>2" unfolding split drop_append lo_simps
    unfolding drop_replicate diff_self_eq_0 by simp
  also have "... = up" using \<open>ends_in True up\<close> by (rule bin_nat_bin)
  finally show "drop k ?lhs = up" .
qed


lemma suffix_len_eq:
  fixes up lo k :: nat
  assumes "up > 0"
    and "lo < 2^k"
  defines "n' \<equiv> up * 2^k"
  defines "n \<equiv> n' + lo"
  shows "bit_length n = bit_length n'" (is "?l n = ?l n'")
proof (cases "lo > 0")
  assume "lo > 0"
  have "k > 0" proof (rule ccontr)
    assume "\<not> 0 < k"
    then have "k = 0" by simp
    with \<open>lo < 2^k\<close> have "lo = 0" by simp
    with \<open>lo > 0\<close> show False by simp
  qed

  let ?up = "bin_of_nat up" and ?lo = "bin_of_nat lo"
    and ?z = "\<lambda>k. False \<up> k" and ?lb = "\<lambda>n. length (bin_of_nat n)"

  from \<open>up > 0\<close> have "n' > 0" unfolding n'_def by simp
  then have "n > 0" unfolding n_def by simp

  from n'_def have n'_eq: "n' = up * 2^k + 0" by simp

  from \<open>lo < 2^k\<close> have "lo \<le> 2^k - 1" by simp
  then have "nat_log 2 lo \<le> nat_log 2 (2^k - 1)" ..

  have "?lb lo = nat_log 2 lo + 1" using \<open>lo > 0\<close> by (rule bit_len_eq_log2)
  also have "... \<le> nat_log 2 (2^k - 1) + 1" using \<open>nat_log 2 lo \<le> nat_log 2 (2^k - 1)\<close> by (rule add_right_mono)
  also have "... = k" unfolding log2.exp_m1 using \<open>k > 0\<close> by (subst le_add_diff_inverse2) force+
  finally have "?lb lo \<le> k" .

  have "bin_of_nat n' = ?z k @ ?up" unfolding n'_eq using add_suffix_bin'[of up 0 k] \<open>up > 0\<close> zero_less_power pos2 by simp
  with arg_cong have "?lb n' = length (?z k @ ?up)" .
  also have "... = length (?lo @ ?z (k - ?lb lo) @ ?up)"
    unfolding length_append length_replicate add.assoc[symmetric] \<open>k \<ge> ?lb lo\<close>[THEN le_add_diff_inverse] ..
  also have "... = ?lb n"
  proof (rule arg_cong[where f=length], rule sym)
    show "bin_of_nat n = ?lo @ ?z (k - ?lb lo) @ ?up" unfolding n_def n'_def using add_suffix_bin' \<open>up > 0\<close> \<open>lo < 2^k\<close> .
  qed
  finally show "?lb n = ?lb n'" ..
qed \<comment> \<open>case \<open>lo = 0\<close> by\<close> (simp add: assms)


lemma adj_sq_sh_pfx_half:
  assumes len: "length w \<ge> 9" \<comment> \<open>lower bound for \<open>4 + l div 2 < l\<close>\<close>
  defines k: "k \<equiv> suffix_len w"
  defines w': "w' \<equiv> adj_sq\<^sub>w w"
  shows "shared_MSBs (length w - k) w w'"
proof (intro sh_msbI)
  define n where n: "n = gn w"
  define w\<^sub>n where wn_def: "w\<^sub>n = bin_of_nat n"
  have "n > 0" unfolding n by (rule gn_gt_0)
  have wn: "w\<^sub>n = w @ [True]" unfolding n wn_def gn_def by (subst bin_nat_bin) blast+

  define ps where ps: "ps \<equiv> drop k w\<^sub>n"
  define up where up: "up = (ps)\<^sub>2"
  define lo where lo: "lo = n mod 2^k"
  define n' where n': "n' = n - lo"
  let ?lo = "bin_of_nat lo" and ?up = "bin_of_nat up"

  from len have "k \<le> length w" unfolding k by (rule suffix_min_len)
  then have "up > 0" unfolding up ps wn by force
  have "lo < 2 ^ k" unfolding lo using zero_less_power pos2 by (intro pos_mod_bound)
  then have "bit_length lo \<le> k" by (rule bit_len_le_pow2)

  have "ends_in True w\<^sub>n" unfolding wn ..
  moreover from \<open>k \<le> length w\<close> have "k < length w\<^sub>n" unfolding wn_def n len_gn by simp
  ultimately have "ends_in True ps" unfolding ps ..

  have n'_split: "n' = up * 2^k" unfolding up wn_def ps n' lo
    unfolding nat_of_bin_drop nat_bin_nat by (rule minus_mod_eq_div_mult)
  have n_split: "n = up * 2^k + lo" by (fold n'_split, unfold lo n', simp)

  have l_eq: "bit_length n = bit_length n'" unfolding n_split n'_split
    using \<open>up > 0\<close> \<open>lo < 2 ^ k\<close> by (rule suffix_len_eq)

  define sq where sq: "sq = adj_square n"
  define sq_diff where "sq_diff = sq - n'"
  have sq_w': "bin_of_nat sq = w' @ [True]" unfolding w' adj_sq\<^sub>w_def sq n
    by (subst gn_inv_of_bin) (rule adj_sq_gt_0, fact refl)

  have sq_eq: "sq = next_square n'" unfolding sq adj_square_def n' lo k n gn_inv_id ..
  have sq_split: "sq = up * 2^k + sq_diff" unfolding sq_diff_def n'_split[symmetric] sq_eq
    using next_sq_correct2[of n'] by (subst add_diff_inverse_nat) (elim leD, blast)
  have "sq_diff < 2 ^ (4 + bit_length n' div 2)" unfolding sq_diff_def sq_eq suffix_len_def
    using next_sq_diff .
  also have "... \<le> 2 ^ k" unfolding l_eq[symmetric] n len_gn k suffix_len_def
    by (intro power_increasing, cases "even (length w)") force+
  finally have "sq_diff < 2 ^ k" .

  from adj_sq_gt_0 have *: "bit_length (adj_square x) \<ge> 1" for x
    unfolding One_nat_def by (intro Suc_leI) fast

  have "length w + 1 = length w\<^sub>n" unfolding wn by simp
  also have "... = bit_length n" unfolding wn_def ..
  also have "... = bit_length n'" by (rule l_eq)
  also have "... = bit_length sq" unfolding n'_split sq_split
    using \<open>up > 0\<close> \<open>sq_diff < 2 ^ k\<close> by (rule suffix_len_eq[symmetric])
  also have "... = length w' + 1" unfolding w' sq n unfolding adj_sq\<^sub>w_def len_gn_inv
    unfolding nat_minus_add_max using * by (subst max_absorb1) blast+
  finally show l: "length w' = length w" by simp

  have lk: "length w - (length w - k) = k" using \<open>length w \<ge> k\<close> by (rule diff_diff_cancel)
  have lwl: "k - length w = 0" by (subst lk[symmetric]) force

  have "drop k w\<^sub>n = drop k (bin_of_nat ((?up)\<^sub>2 * 2 ^ k + (?lo)\<^sub>2))" unfolding wn_def n_split nat_bin_nat ..
  also have "... = ps" unfolding up
    using \<open>lo < 2 ^ k\<close> \<open>ends_in True ps\<close> by (subst drop_suffix_bin) force+
  also have "... = drop k (bin_of_nat ((?up)\<^sub>2 * 2 ^ k + (bin_of_nat sq_diff)\<^sub>2))" unfolding up
    using \<open>sq_diff < 2 ^ k\<close> \<open>ends_in True ps\<close> by (subst drop_suffix_bin) force+
  also have "... = drop k (bin_of_nat sq)" unfolding sq_split nat_bin_nat ..
  finally have "drop k w = drop k w'" unfolding wn sq_w' drop_append lwl l[symmetric] by blast
  then show "drop (length w' - (length w - k)) w' = drop (length w - (length w - k)) w"
    unfolding l lk ..
qed


lemma sh_pfx_log_ineq: "l \<ge> 20 \<Longrightarrow> nat_log 2 l \<le> l div 2 - 6"
proof (induction l rule: nat_induct_at_least)
  case base (* l = 20 *)
  show ?case by (simp add: Discrete.log.simps)
next
  case (Suc n)
  let ?Sn = "Suc n"
  from \<open>n \<ge> 20\<close> have "n \<noteq> 0" "n > 0" by linarith+
  from log2.Suc \<open>n > 0\<close> have log2_Suc': "nat_log 2 ?Sn = (if ?Sn = 2 ^ nat_log 2 ?Sn then Suc (nat_log 2 n) else nat_log 2 n)" .

  note remove_plus1 = nat.inject[unfolded Suc_eq_plus1] Suc_le_mono[unfolded Suc_eq_plus1]

  show ?case proof (cases "?Sn = 2 ^ nat_log 2 ?Sn")
    case True
    note * = log2_Suc'[unfolded if_P[OF this]]
    have "even ?Sn" by (subst \<open>?Sn = 2 ^ nat_log 2 ?Sn\<close>) (force simp: *)
    then have div_eq: "?Sn div 2 = n div 2 + 1" by force

    have "nat_log 2 ?Sn = (nat_log 2 n) + 1" by (force simp: *)
    also have "... \<le> n div 2 - 6 + 1" unfolding remove_plus1 using Suc.IH .
    also have "... = n div 2 + 1 - 6" using \<open>n \<ge> 20\<close> by (intro add_diff_assoc2) linarith
    also have "... = ?Sn div 2 - 6" unfolding div_eq ..
    finally show ?thesis .
  next
    case False
    then have "nat_log 2 ?Sn = nat_log 2 n" by (subst log2_Suc') simp
    also have "... \<le> n div 2 - 6" unfolding remove_plus1 using Suc.IH .
    also have "... \<le> ?Sn div 2 - 6" by (intro diff_le_mono) (rule Suc_div_le_mono)
    finally show ?thesis .
  qed
qed

lemma sh_pfx_log_ineq':
  assumes "l \<ge> 20"
  defines "l_div_2 \<equiv> l div 2"
  shows "nat_log_ceil 2 l \<le> l div 2 - 5"
proof -
  have "l div 2 \<ge> 6" using \<open>l \<ge> 20\<close> by linarith

  have "nat_log_ceil 2 l \<le> nat_log 2 l + 1" by (fact log2.ceil_le_nat_log_p1)
  also have "... \<le> l div 2 - 6 + 1" unfolding add_le_cancel_right
    using \<open>l \<ge> 20\<close> by (rule sh_pfx_log_ineq)
  also have "... = l div 2 + 1 - 6" using \<open>l div 2 \<ge> 6\<close> by (rule add_diff_assoc2)
  also have "... = l div 2 - (6 - 1)" using \<open>l div 2 \<ge> 6\<close> by (intro diff_diff_right[symmetric]) simp
  also have "... = l div 2 - 5" by force
  finally show ?thesis .
qed


theorem adj_sq_sh_pfx_log:
  fixes w
  defines "l \<equiv> length w"
  defines "w' \<equiv> adj_sq\<^sub>w w"
  assumes "l \<ge> 20" \<comment> \<open>lower bound for \<open>clog l \<le> l div 2 - 5\<close>\<close>
  shows "shared_MSBs (nat_log_ceil 2 l) w w'"
proof -
  have "nat_log_ceil 2 l \<le> l div 2 - 5" using \<open>l \<ge> 20\<close> by (rule sh_pfx_log_ineq')
  also have "... = l div 2 + l div 2 - l div 2 - 5" unfolding diff_add_inverse2 ..
  also have "... \<le> l - l div 2 - 5" by (intro diff_le_mono) (fold mult_2, simp)
  also have "... = l - (5 + l div 2)" unfolding diff_diff_left by presburger
  also have "... = length w - suffix_len w" unfolding suffix_len_def len_gn l_def[symmetric] ..
  finally have "nat_log_ceil 2 l \<le> length w - suffix_len w" .

  moreover have "shared_MSBs (length w - suffix_len w) w (adj_sq\<^sub>w w)" using \<open>l \<ge> 20\<close>
    by (intro adj_sq_sh_pfx_half) (fold l_def, force)
  ultimately show "shared_MSBs (nat_log_ceil 2 l) w w'" by (fold w'_def) (rule sh_msb_le)
qed


end
