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

lemma member_SQ_SQ_nat: "w \<in>\<^sub>L SQ \<longleftrightarrow> gn w \<in> SQ_nat" by simp

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

    from \<open>gn w \<le> x\<close> have "dsqrt (gn w) \<le> dsqrt x" by (rule mono_floor_sqrt')
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
    from \<open>gn w = z\<^sup>2\<close> and \<open>z \<le> dsqrt x\<close> show "gn w \<le> x" using le_floor_sqrt_iff by simp
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
  unfolding sqrt_def using pos2 \<open>x > 0\<close> by (simp add: log_root)

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

lemma adj_sq_diff_pow2: "2 * dsqrt n + 1 < 2 ^ (4 + (bit_length n - 1) div 2)"
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

  also have "... \<le> 2 ^ (4 + (bit_length n - 1) div 2)" using \<open>n > 0\<close> by (subst bit_len_eq_log2) auto
  finally show ?thesis .
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp

lemma adj_sq_diff: "next_square n - prev_square n < 2 ^ (4 + (bit_length n - 1) div 2)"
  using adj_sq_diff_pow2 next_prev_sq_diff by (rule dual_order.strict_trans2)

lemma next_sq_diff: "next_square n - n < 2 ^ (4 + (bit_length n - 1) div 2)"
  using adj_sq_diff_pow2 next_sq_diff by (rule dual_order.strict_trans2)


subsection\<open>Adjacent Square\<close>

definition suffix_len :: "bin \<Rightarrow> nat"
  where "suffix_len w \<equiv> 4 + length w div 2"

lemma suffix_min_len: "length w \<ge> 7 \<Longrightarrow> suffix_len w \<le> length w" unfolding suffix_len_def by linarith

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
lemma pow2_min: "0 < n \<Longrightarrow> n < 2^k \<Longrightarrow> k > 0" for n k :: nat by (rule ccontr) force+

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
  assumes len: "length w \<ge> 7" \<comment> \<open>lower bound for \<open>4 + l div 2 < l\<close>\<close>
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
  have "lo < 2 ^ k" unfolding lo using zero_less_power pos2 by simp
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
  have "sq_diff < 2 ^ (4 + (bit_length n' - 1) div 2)" unfolding sq_diff_def sq_eq suffix_len_def
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


lemma sh_pfx_log_ineq: "l \<ge> 18 \<Longrightarrow> nat_log 2 l \<le> l div 2 - 5"
proof (induction l rule: nat_induct_at_least)
  case base (* l = 18 *)
  show ?case by (simp add: Discrete_Functions.floor_log.simps)
next
  case (Suc n)
  let ?Sn = "Suc n"
  from \<open>n \<ge> 18\<close> have "n \<noteq> 0" "n > 0" by linarith+
  from log2.Suc \<open>n > 0\<close> have log2_Suc': "nat_log 2 ?Sn = (if ?Sn = 2 ^ nat_log 2 ?Sn then Suc (nat_log 2 n) else nat_log 2 n)" .

  note remove_plus1 = nat.inject[unfolded Suc_eq_plus1] Suc_le_mono[unfolded Suc_eq_plus1]

  show ?case proof (cases "?Sn = 2 ^ nat_log 2 ?Sn")
    case True
    note * = log2_Suc'[unfolded if_P[OF this]]
    have "even ?Sn" by (subst \<open>?Sn = 2 ^ nat_log 2 ?Sn\<close>) (force simp: *)
    then have div_eq: "?Sn div 2 = n div 2 + 1" by force

    have "nat_log 2 ?Sn = (nat_log 2 n) + 1" by (force simp: *)
    also have "... \<le> n div 2 - 5 + 1" unfolding remove_plus1 using Suc.IH .
    also have "... = n div 2 + 1 - 5" using \<open>n \<ge> 18\<close> by (intro add_diff_assoc2) linarith
    also have "... = ?Sn div 2 - 5" unfolding div_eq ..
    finally show ?thesis .
  next
    case False
    then have "nat_log 2 ?Sn = nat_log 2 n" by (subst log2_Suc') simp
    also have "... \<le> n div 2 - 5" unfolding remove_plus1 using Suc.IH .
    also have "... \<le> ?Sn div 2 - 5" by (intro diff_le_mono) (rule Suc_div_le_mono)
    finally show ?thesis .
  qed
qed

definition SQ' :: "bool list lang" where
  "SQ' \<equiv> Lang {w. length w = 2} (\<lambda>w. \<exists>x. gn' w = x\<^sup>2)"

lemma alphabet_SQ'_subset [intro]: "alphabet SQ' \<subseteq> {w. length w = 2}"
  unfolding SQ'_def by simp

lemma member_SQ'[simp]: "w \<in>\<^sub>L SQ' \<longleftrightarrow> (\<exists>x. set w \<subseteq> {w. length w = 2} \<and> gn' w = x\<^sup>2)"
  by (simp add: SQ'_def)

lemma gn'_in_SQ_nat_iff [iff]: "gn' w \<in> SQ_nat \<longleftrightarrow> (\<exists>x. gn' w = x\<^sup>2)"
  unfolding SQ_nat_def gn'_def by simp

lemma member_SQ'_SQ_nat: "set w \<subseteq> {w. length w = 2} \<Longrightarrow>
                          w \<in>\<^sub>L SQ' \<longleftrightarrow> gn' w \<in> SQ_nat" by simp

text\<open>Relating \<^const>\<open>SQ\<close> and \<^const>\<open>SQ_nat\<close>:\<close>
lemma SQ'_SQ_nat_eq: "words SQ' = {w. set w \<subseteq> {w. length w = 2} \<and> gn' w \<in> SQ_nat}"
  by auto

lemma SQ'_nat_im: "SQ_nat = gn' ` words SQ'"
proof (intro subset_antisym subsetI image_eqI CollectI)
  fix n assume "n \<in> SQ_nat"
  then have "n > 0" by simp
  then show "n = gn'(gn'_inv n)" by simp

  from \<open>n \<in> SQ_nat\<close> have "\<exists>x. n = x ^ 2" by simp
  then obtain x where b: "n = x ^ 2" ..
  with \<open>n > 0\<close> show "gn'_inv n \<in>\<^sub>L SQ'" unfolding SQ'_def gn'_inv_def apply auto
    using bin'_wf_def apply blast
    using \<open>n = gn' (gn'_inv n)\<close> gn'_inv_def by auto
next
  fix n
  assume "n \<in> gn' ` words SQ'"
  then have "n > 0" using gn_gt_0 by blast
  from \<open>n \<in> gn' ` words SQ'\<close> have "n \<in> {n. \<exists>x. gn' (gn'_inv n) = x ^ 2}"
    using gn'_inv_id by fastforce
  then have "\<exists>x. gn' (gn'_inv n) = x ^ 2" by blast
  then obtain x where "gn' (gn'_inv n) = x ^ 2" ..
  with \<open>n > 0\<close> have "n = x ^ 2" using inv_gn_id by simp
  with \<open>n > 0\<close> show "n \<in> SQ_nat" by simp
qed


text\<open>``Lemma 4.2 @{cite rassOwf2017}. The language of squares \<open>SQ = {y. y = x\<^sup>2 \<and> x \<in> \<nat>}\<close>
  has a density function \<open>dens\<^sub>S\<^sub>Q(x) \<in> \<Theta>(\<surd>x)\<close>.''\<close>

theorem dens'_SQ': "dens' SQ' x = dsqrt x"
proof -
  have eq: "{w\<in> words SQ'. gn' w \<le> x} = gn'_inv ` power2 ` {0<..dsqrt x}"
  proof (intro subset_antisym subsetI image_eqI CollectI conjI)
    fix w
    assume "w \<in> {w \<in> words SQ'. gn' w \<le> x}"
    then have "w \<in>\<^sub>L SQ'" and "gn' w \<le> x" by blast+

    show "w = gn'_inv (gn' w)" using \<open>w \<in>\<^sub>L SQ'\<close>
      by (metis (mono_tags, lifting) bin'_wf_def gn'_inv_id mem_Collect_eq
          member_SQ' subsetD)

    from \<open>w \<in>\<^sub>L SQ'\<close> obtain z where "gn' w = z\<^sup>2" unfolding SQ'_def by auto
    then have "z = dsqrt (gn' w)" by simp
    then show "gn' w = (dsqrt (gn' w))\<^sup>2" using \<open>gn' w = z\<^sup>2\<close> by blast

    from \<open>gn' w \<le> x\<close> have "dsqrt (gn' w) \<le> dsqrt x" by (rule mono_floor_sqrt')
    moreover have "dsqrt (gn' w) > 0" using gn_gt_0 by simp
    ultimately show "dsqrt (gn' w) \<in> {0<..dsqrt x}" by simp
  next
    fix w
    assume a: "w \<in> gn'_inv ` power2 ` {0<..dsqrt x}"
    then obtain z where zw: "w = gn'_inv (z\<^sup>2)" and zx: "z \<in> {0<..dsqrt x}" by blast
    from zx have "z > 0" and "z \<le> dsqrt x" unfolding greaterThanAtMost_iff by blast+
    have 1: "set w \<subseteq> {w. length w = 2}" using a unfolding gn'_inv_def apply auto
      using bin'_wf_def by blast
    from zw have "gn' w = gn' (gn'_inv (z\<^sup>2))" by blast
    also have "... = z\<^sup>2" using inv_gn'_id zero_less_power \<open>z > 0\<close> .
    finally have "gn' w = z\<^sup>2" .
    then show "w \<in>\<^sub>L SQ'" unfolding SQ'_def using 1 by simp
    from \<open>gn' w = z\<^sup>2\<close> and \<open>z \<le> dsqrt x\<close> show "gn' w \<le> x" using le_floor_sqrt_iff by simp
  qed
  have SQ'_true_false: "alphabet SQ' \<subseteq> {w. length w = 2}"
    unfolding SQ'_def by simp
  have "power2 ` {0<..dsqrt x} \<subseteq> {0<..}" by auto
  with inj_on_subset gn'_inv_inj have "inj_on gn'_inv (power2 ` {0<..dsqrt x})" .
  with card_image have "dens' SQ' x = card (power2 ` {0<..dsqrt x})"
    unfolding dens'_def [OF SQ'_true_false] eq .
  also have "\<dots> = card {0<..dsqrt x}" by (intro card_image, unfold inj_on_def) fastforce
  also have "\<dots> = dsqrt x" by simp
  finally show ?thesis .
qed

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

lemma adj_sq_diff_pow2': "2 * dsqrt n + 1 < 2 ^ (4 + (bit'_length n - 1) div 2)"
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

  also have "... \<le> 2 ^ (4 + (bit'_length n - 1) div 2)" using \<open>n > 0\<close>
    by (subst bit'_len_eq_log2) auto
  finally show ?thesis .
qed \<comment> \<open>case \<open>n = 0\<close> by\<close> simp

lemma adj_sq_diff': "next_square n - prev_square n < 2 ^ (4 + (bit'_length n - 1) div 2)"
  using adj_sq_diff_pow2' next_prev_sq_diff by (rule dual_order.strict_trans2)

lemma next_sq_diff': "next_square n - n < 2 ^ (4 + (bit'_length n - 1) div 2)"
  using adj_sq_diff_pow2' Discrete_Sqrt.next_sq_diff by (rule dual_order.strict_trans2)


subsection\<open>Adjacent Square\<close>

definition suffix'_len :: "bin' \<Rightarrow> nat"
  where "suffix'_len w \<equiv> 3 + length w div 2"

lemma suffix'_min_len: "length w \<ge> 7 \<Longrightarrow> suffix'_len w \<le> length w"
  unfolding suffix'_len_def by linarith

definition adj_square' :: "nat \<Rightarrow> nat"
  where "adj_square' n = next_square (n - n mod 4^(suffix'_len (gn'_inv n)))"

lemma adj_square'_1: "n < 4^(suffix'_len (gn'_inv n)) \<Longrightarrow> adj_square' n = Suc 0"
  unfolding adj_square'_def
proof -
  assume a1: "n < 4 ^ suffix'_len (gn'_inv n)"
  have 1: "n mod 4 ^ suffix'_len (gn'_inv n) = n" using a1 by simp
  have 2: "n - n mod 4 ^ suffix'_len (gn'_inv n) = 0" unfolding 1 by simp
  show "next_square (n - n mod 4 ^ suffix'_len (gn'_inv n)) = Suc 0"
    unfolding 2 by simp
qed

lemma bit_length_mod_pow2: "bit_length (n mod 2^k) \<le> k"
  by (simp add: bit_len_le_pow2)

lemma length_bin'_of_nat_mod_pow4: "length (bin'_of_nat (n mod 4^k)) \<le> k"
  apply (induction k)
   apply simp
  by (meson length_bin'_of_nat_le_iff mod_less_divisor zero_less_numeral
      zero_less_power)

lemma nmn_mod_m_ge_m: "(n::nat) \<ge> m \<Longrightarrow> n - n mod m \<ge> m"
  by (metis bot_nat_0.extremum_uniqueI div_greater_zero_iff
      linorder_le_less_linear minus_mod_div nless_le)

lemma bin_of_nat_nmn_mod_pow2m: "bin_of_nat (n - n mod 2^m) =
       trimRight False ((replicate m False) @ (drop m (bin_of_nat n)))"
  by (metis ExtBinary.bin'_of_nat.simps ExtBinary.nat_bin'_nat bin_nat_bin_drop_zs
      minus_mod_eq_div_mult nat_of_bin_app_0s nat_of_bin_drop nat_of_bin_via_bin')

lemma bin_of_nat_nmn_mod_pow4m: "bin_of_nat (n - n mod 4^m) =
       trimRight False ((replicate (2 * m) False) @ (drop (2 * m) (bin_of_nat n)))"
  using bin_of_nat_nmn_mod_pow2m
  by (metis numeral_Bit0_eq_double power2_eq_square power_mult)

lemma nmn_mod_pow4m_nat_of_bin: "n - n mod 4^m =
                                 ((replicate (2 * m) False) @
                                 (drop (2 * m) (bin_of_nat n)))\<^sub>2"
  using bin_of_nat_nmn_mod_pow4m by (metis bin_nat_bin_drop_zs nat_bin_nat)

(*
 * Choose the adjacent square of \<open>n\<close> as the \<open>next_square\<close> of the smallest number sharing its prefix.
 * That is, the prefix concatenated with zeroes to have the same length as \<open>n\<close>.
 *)

lemma adj_sq'_correct': "gn'_inv (adj_square' n) \<in>\<^sub>L SQ'"
  using adj_sq_gt_0 adj_sq_correct unfolding adj_square'_def gn'_inv_def
    suffix'_len_def SQ'_def gn'_def apply auto
  using bin'_wf_def by blast


definition adj_sq\<^sub>w' :: "word' \<Rightarrow> word'"
  where [simp]: "adj_sq\<^sub>w' w \<equiv> gn'_inv (adj_square' (gn' w))"

theorem adj_sq'_word'_correct: "adj_sq\<^sub>w' w \<in>\<^sub>L SQ'" unfolding adj_sq\<^sub>w'_def
  using adj_sq'_correct' adj_sq_gt_0 by simp

lemma bin'_wf_adj_sq\<^sub>w'I [intro]: "bin'_wf w \<Longrightarrow> bin'_wf (adj_sq\<^sub>w' w)"
  unfolding adj_sq\<^sub>w'_def gn'_defs gn_defs by blast


subsection\<open>Shared Prefix\<close>

definition shared_MSBs' :: "nat \<Rightarrow> bin' \<Rightarrow> bin' \<Rightarrow> bool"
  where "shared_MSBs' l a b \<equiv> length b = length a \<and> take l b = take l a"


mk_ide shared_MSBs'_def |intro sh'_msbI[intro]| |dest sh'_msbD[dest]|

lemma sh'_msb_le:
  assumes "L \<ge> l"
    and shL: "shared_MSBs' L a b"
  shows "shared_MSBs' l a b"
  using assms unfolding shared_MSBs'_def by (metis min.orderE take_take)

lemma sh'_msb_comm:
  "shared_MSBs' l a b \<Longrightarrow> shared_MSBs' l b a" unfolding shared_MSBs'_def by argo

lemma shared_MSBs'_imp_prefix1: "shared_MSBs' l a b \<Longrightarrow> prefix (take l a) b"
  apply (rule prefixI [where zs="drop l b"])
  unfolding shared_MSBs'_def apply (erule conjE)
  apply (erule subst [where s="take l b"]) by simp

lemma shared_MSBs'_imp_prefix2: "shared_MSBs' l a b \<Longrightarrow> prefix (take l b) a"
  using sh'_msb_comm shared_MSBs'_imp_prefix1 by simp

lemma bit'_len_le_pow2: "n < 2 ^ k \<Longrightarrow> bit'_length n \<le> k"
proof (cases "n > 0", cases "k > 0")
  assume "n > 0" and "k > 0" and "n < 2 ^ k"
  from \<open>n > 0\<close> \<open>n < 2 ^ k\<close> have "n \<le> 2 ^ k - 1" by linarith

  from \<open>n > 0\<close> have "bit'_length n = nat_log 2 n + 1" by (rule bit'_len_eq_log2)
  also have "... \<le> nat_log 2 (2 ^ k - 1) + 1" unfolding add_le_cancel_right
    using \<open>n \<le> 2 ^ k - 1\<close> by (rule nat_log_le_iff)
  also have "... = k" unfolding log2.exp_m1 using \<open>k > 0\<close> by simp
  finally show ?thesis .
qed \<comment> \<open>cases \<open>n = 0\<close> and \<open>k = 0\<close> by\<close> fastforce+

(* suppl *)
lemma add_suffix'_bin:
  fixes up lo k :: nat
  assumes "lo < 4^k"
  shows "up * 4^k + lo = nat_of_bin' ((bin'_of_nat up) @
        ([False, False] \<up> (k - (length (bin'_of_nat lo)))) @ (bin'_of_nat lo))"
    (is "?lhs = nat_of_bin' (?up @ ?zs @ ?lo)")
proof (cases "up > 0", cases "lo > 0")
  assume "up > 0" and "lo > 0"
  let ?n = nat_of_bin'
    and ?b = bin_of_nat
    and ?z = "\<lambda>l. False \<up> l"

  have "k > 0" using \<open>lo > 0\<close> \<open>lo < 4^k\<close>
    using zero_less_iff_neq_zero by fastforce
  have 1: "length (bin'_of_nat (4 ^ k)) = Suc k"
    apply simp
    apply (induction k)
     apply auto
    by (metis (no_types, lifting) One_nat_def add.commute bin_of_nat.simps(1)
        bin_of_nat_double bot_nat_0.not_eq_extremum div2_Suc_Suc div_less list.size(3)
        list.size(4) log2.valid_base mult_numeral_left_semiring_numeral nat.simps(3)
        numeral_Bit0_eq_double numeral_times_numeral plus_1_eq_Suc)
  have 2: "n \<le> m \<Longrightarrow> length (bin'_of_nat n) \<le> length (bin'_of_nat m)" for n m :: nat
    apply (induction n)
     apply auto
    by (metis ExtBinary.lengths_le Suc_le_mono bin_of_nat.simps(2) div_le_mono)
  have 3: "Suc (4 ^ k - 1) = 4 ^ k" by simp
  have 4: "bin'_of_nat (4 ^ k) = [False, True]#(replicate k [False, False])"
    by (rule bin'_of_nat_4_pow)
  have 5: "inc' ([True, True] \<up> k) = [False, True]#(replicate k [False, False])"
    by (rule inc'_repl_TT)
  have 6: "(0::nat) < 4 ^ k - 1"
  proof -
    obtain k' :: nat where k_def: "k = Suc k'" using \<open>k > 0\<close> by (rule lessE)
    have "(4::nat) ^ k' \<ge> 1" by simp
    hence "(4::nat) ^ k \<ge> 4" unfolding k_def by simp
    thus "(0::nat) < 4 ^ k - 1" by simp
  qed
  have 7: "starts_with_True ([True, True] \<up> k)" using \<open>k > 0\<close>
    by (metis bot_nat_0.not_eq_extremum hd_replicate list.sel(1) list.set_intros(1)
        replicate_empty starts_with_True.elims(3))
  have 8: "bin'_of_nat (4 ^ k - 1) = replicate k [True, True]"
    using 4 unfolding inc'_repl_TT [symmetric] apply (subst (asm) 3 [symmetric])
    unfolding bin'_of_nat_Suc_inc' using inc'_inj [of "bin'_of_nat (4 ^ k - 1)"
        "[True, True] \<up> k", OF bin'_of_nat_wf bin'_wf_replicate_2_bits
        bin'_of_nat_gt_0_start_True [OF 6] 7] by blast
  have 9: "length (bin'_of_nat lo) \<le> k" using \<open>lo < 4^k\<close> using 8
    by (metis 2 3 length_replicate less_Suc_eq_le)
  have lloz: "length (?zs @ ?lo) = k" using le_add_diff_inverse [OF 9] by simp
  have "?n (?up @ ?zs @ ?lo) = ?n ((?up @ ?zs) @ ?lo)" unfolding append_assoc ..
  also have "... = up * 4 ^ length (?zs @ ?lo) + lo" unfolding nat_of_bin'_app
    unfolding nat_bin'_nat nat_of_bin'_0s [where n=2, unfolded bin'_repl] apply simp
    unfolding bin'_repl [symmetric]
    by (simp add: group_2_bin'_wf power_add power_mult)
  also have "... = ?lhs" unfolding lloz ..
  finally show ?thesis by (rule sym)
next
  assume a1: "0 < up" and a2: "\<not>0 < lo"
  have 1: "lo = 0" using a2 by simp
  hence 2: "bin'_of_nat lo = []" by simp
  show "up * 4 ^ k + lo = nat_of_bin' (bin'_of_nat up @
        [False, False] \<up> (k - length (bin'_of_nat lo)) @ bin'_of_nat lo)"
    unfolding 2 unfolding 1
    by (metis ExtBinary.nat_bin'_nat ExtBinary.nat_of_bin'_app_0s
        add.right_neutral bin'_repl diff_zero list.size(3) numeral_Bit0_eq_double
        power2_eq_square power_mult self_append_conv)
next
  show "\<not> 0 < up \<Longrightarrow> up * 4 ^ k + lo = nat_of_bin' (bin'_of_nat up @
        [False, False] \<up> (k - length (bin'_of_nat lo)) @ bin'_of_nat lo)"
    by (metis ExtBinary.nat_bin'_nat ExtBinary.nat_of_bin'_0s
        ExtBinary.nat_of_bin'_app add_cancel_left_left bin'_repl gr0I mult_is_0)
qed

corollary add_suffix'_bin':
  fixes up lo k :: nat
  assumes "up > 0" \<comment> \<open>required to prevent leading zeroes\<close>
    and "lo < 4^k"
  shows "bin'_of_nat (up * 4^k + lo) = (bin'_of_nat up) @
        ([False, False] \<up> (k - (length (bin'_of_nat lo)))) @ (bin'_of_nat lo)"
    (is "?lhs = ?up @ ?zs @ ?lo")
proof -
  from \<open>up > 0\<close> have "starts_with_True ?up" unfolding bin'_of_nat_start_True .
  moreover from \<open>up > 0\<close> have "?up \<noteq> []" using calculation by auto
  ultimately have 1: "starts_with_True (?up @ ?zs @ ?lo)"
    unfolding starts_with_append apply auto
    using starts_with_True_app by force
  have 2: "bin'_wf (bin'_of_nat up @ [False, False] \<up> (k - length (bin'_of_nat lo)) @
           bin'_of_nat lo)"
    apply (rule bin'_wf_appI)
     apply blast
    apply (rule bin'_wf_appI)
    by auto
  have "?up @ ?zs @ ?lo = bin'_of_nat (nat_of_bin' (?up @ ?zs @ ?lo))"
    using bin'_nat_bin'[symmetric, OF 1 2] .
  also have "... = ?lhs" using add_suffix'_bin[of lo k up] assms by presburger
  finally show ?thesis by (rule sym)
qed


lemma drop_suffix'_bin':
  fixes lo up :: bin' and k :: nat
  assumes "starts_with_True up" and up_subset: "set up \<subseteq> {w. length w = 2}" and
    lo: "nat_of_bin' lo < 4 ^ k"
  shows "take (length up) (bin'_of_nat ((nat_of_bin' up) * 4^k + (nat_of_bin' lo))) = up"
    (is "take (length up) ?lhs = up")
proof -
  from \<open>starts_with_True up\<close> have up: "nat_of_bin' up > 0"
    by (rule nat_of_bin'_gt_0_start_True)
  from \<open>nat_of_bin' lo < 4 ^ k\<close> have "length (bin'_of_nat (nat_of_bin' lo)) \<le> k"
    using length_bin'_of_nat_le_iff by simp
  then have drop_k_lo: "drop k (bin'_of_nat (nat_of_bin' lo)) = []" by (rule drop_all)

  let ?lo = "bin'_of_nat (nat_of_bin' lo)"
  let ?loz = "[False, False] \<up> (k - length ?lo) @ ?lo"

  have lo_simps: "length ?loz = k" "drop k ?lo = []"
    using \<open>length (bin'_of_nat (nat_of_bin' lo)) \<le> k\<close> by force+
  have "?lhs = bin'_of_nat (nat_of_bin' up) @ ?loz" unfolding append.assoc
    using \<open>nat_of_bin' up > 0\<close> \<open>nat_of_bin' lo < 4 ^ k\<close> add_suffix'_bin' by blast
  hence split: "?lhs = up @ ?loz"
    using ExtBinary.bin'_nat_bin' assms(1) assms(2) by (metis set_all_length_2_wf)
  have "take (length up) ?lhs = bin'_of_nat (nat_of_bin' up)"
    unfolding split using ExtBinary.bin'_nat_bin' assms(1) up_subset
    by (metis append_eq_conv_conj set_all_length_2_wf)
  also have "... = up" using \<open>starts_with_True up\<close> bin'_nat_bin' assms(2)
    set_all_length_2_wf by blast
  finally show "take (length up) ?lhs = up" .
qed

lemma suffix'_len_eq:
  fixes up lo k :: nat
  assumes "up > 0"
    and "lo < 4^k"
  defines "n' \<equiv> up * 4^k"
  defines "n \<equiv> n' + lo"
  shows "length (bin'_of_nat n) = length (bin'_of_nat n')" (is "?l n = ?l n'")
proof (cases "lo > 0")
  assume "lo > 0"
  have "k > 0" proof (rule ccontr)
    assume "\<not> 0 < k"
    then have "k = 0" by simp
    with \<open>lo < 4^k\<close> have "lo = 0" by simp
    with \<open>lo > 0\<close> show False by simp
  qed

  let ?up = "bin'_of_nat up" and ?lo = "bin'_of_nat lo"
    and ?z = "\<lambda>k. [False, False] \<up> k" and ?lb = "\<lambda>n. length (bin'_of_nat n)"

  from \<open>up > 0\<close> have "n' > 0" unfolding n'_def by simp
  then have "n > 0" unfolding n_def by simp

  from n'_def have n'_eq: "n' = up * 4^k + 0" by simp

  from \<open>lo < 4^k\<close> have "lo \<le> 4^k - 1" by simp
  then have "nat_log 4 lo \<le> nat_log 4 (4^k - 1)" ..
  have "(4::nat) > 1" by simp

  have "?lb lo = nat_log 4 lo + 1"
    using \<open>4 > 1\<close> \<open>lo > 0\<close>
  proof (induction lo rule: log_induct)
    case (less n)
    hence "n = Suc 0 \<or> n = Suc (Suc 0) \<or> n = Suc (Suc (Suc 0))" by auto
    moreover have "Suc (length (bin_of_nat (Suc 0))) div 2 = Suc 0" by simp
    moreover have "Suc (length (bin_of_nat (Suc (Suc 0)))) div 2 = Suc 0" by simp
    moreover have "Suc (length (bin_of_nat (Suc (Suc (Suc 0))))) div 2 = Suc 0"
      by simp
    ultimately show ?case by auto
  next
    case (div n)
    hence 1: "n div 4 > 0" by linarith
    have "length (bin'_of_nat (n div 4)) = nat_log 4 (n div 4) + 1"
      using div by linarith
    hence "length (bin'_of_nat (4 * (n div 4))) = nat_log 4 (n div 4) + 2"
      by (metis Suc_1 add.left_commute bin'_of_nat_times4 div.hyps
          div_greater_zero_iff length_append_singleton plus_1_eq_Suc rel_simps(51))
    hence "length (bin'_of_nat (4 * (n div 4))) = nat_log 4 n + 1"
      using \<open>1 < 4\<close> div.hyps nat_log_base.intro nat_log_base.rec by presburger
    then show ?case unfolding bin'_of_nat_times4 [OF 1] bin'_of_nat_div4 apply simp
      by (metis Suc_n_div_2_gt_zero Suc_pred bin_of_nat_len_gt_0 div.prems)
  qed
  also have "... \<le> nat_log 4 (4^k - 1) + 1"
    using \<open>nat_log 4 lo \<le> nat_log 4 (4 ^ k - 1)\<close> add_le_mono by blast
  also have "... = k" unfolding log2.exp_m1 using \<open>k > 0\<close>
    Suc_pred' \<open>1 < 4\<close> nat_log_base.exp_m1 nat_log_base.intro by presburger
  finally have "?lb lo \<le> k" .

  have "bin'_of_nat n' = ?up @ ?z k"
    unfolding n'_eq using add_suffix'_bin'[of up 0 k] \<open>up > 0\<close> zero_less_power
      pos2 by simp
  with arg_cong have "?lb n' = length (?up @ ?z k)" .
  also have "... = length (?up @ ?z (k - ?lb lo) @ ?lo)"
    unfolding length_append length_replicate add.assoc[symmetric]
      \<open>k \<ge> ?lb lo\<close>[THEN le_add_diff_inverse]
    using \<open>length (ExtBinary.bin'_of_nat lo) \<le> k\<close> by auto
  also have "... = ?lb n"
  proof (rule arg_cong[where f=length], rule sym)
    show "bin'_of_nat n = ?up @ ?z (k - ?lb lo) @ ?lo"
      unfolding n_def n'_def using add_suffix'_bin' \<open>up > 0\<close> \<open>lo < 4^k\<close> .
  qed
  finally show "?lb n = ?lb n'" ..
qed \<comment> \<open>case \<open>lo = 0\<close> by\<close> (simp add: assms)

lemma bin_times_pow2 [simp]: "ends_in True b \<Longrightarrow>
          bin_of_nat ((nat_of_bin b) * 2^k) = (replicate k False) @ b"
  apply (induction b)
   apply (induction k)
  apply auto
   apply (metis (no_types, lifting) add.commute add.right_neutral append.assoc
      bin_nat_bin left_add_mult_distrib length_replicate mult_0_right
      nat_of_bin.simps(1) nat_of_bin.simps(2) nat_of_bin_0s nat_of_bin_app1
      nat_of_bin_app_0s)
  by (metis append_Cons bin_nat_bin bin_of_nat_app_0s mult.assoc mult.left_commute
      nat_of_bin_app_0s nat_of_bin_gt_0_end_True power_Suc replicate_Suc
      replicate_app_Cons_same)

lemma drop_lower_bin [simp]: "ends_in True b \<Longrightarrow> l < 2^k \<Longrightarrow>
       drop k (bin_of_nat ((nat_of_bin b) * 2^k + l)) = b"
  by (metis drop_suffix_bin nat_bin_nat)

lemma length_bin_pow2_add [simp]: "ends_in True b \<Longrightarrow> l < 2^k \<Longrightarrow>
       length (bin_of_nat ((nat_of_bin b) * 2^k + l)) = length b + k"
  apply (induction l)
  apply (induction k)
  apply auto
   apply (metis add.commute add_Suc_right bin_times_pow2 length_append
      length_append_singleton length_replicate power_Suc)
  by (metis Suc_lessD add_Suc_right bin_of_nat.simps(2) nat_of_bin_gt_0_end_True
      suffix_len_eq)

lemma length_without_add_eq [simp]: "ends_in True b \<Longrightarrow> l < 2^k \<Longrightarrow>
       length (bin_of_nat ((nat_of_bin b) * 2^k + l)) =
       length (bin_of_nat ((nat_of_bin b) * 2^k))" by simp

lemma bin'_times_pow4 [simp]: "starts_with_True b \<Longrightarrow> set b \<subseteq> {w. length w = 2} \<Longrightarrow>
        bin'_of_nat ((nat_of_bin' b) * 4^k) = b @ (replicate k [False, False])"
  apply (induction k)
   apply auto
  using ExtBinary.bin'_nat_bin' set_all_length_2_wf apply force
  by (metis (no_types, lifting) ExtBinary.bin'_of_bin.elims
      ExtBinary.bin'_of_nat.simps append.assoc bin'_of_nat_times4
      bot_nat_0.not_eq_extremum group_2.simps(1) mult.left_commute nat_bin_nat
      nat_of_bin'_gt_0_start_True nat_of_bin.simps(1) nat_of_bin_via_bin'
      replicate_append_same rev.simps(1) starts_with_True_app)

lemma take_bin'_eq [simp]: "starts_with_True b \<Longrightarrow> set b \<subseteq> {w. length w = 2} \<Longrightarrow>
       take (length b) (bin'_of_nat (nat_of_bin' b * 4^k)) = b"
  apply (induction k)
   apply auto
  using ExtBinary.bin'_nat_bin' set_all_length_2_wf apply simp
  by (metis ExtBinary.bin'_of_bin.simps ExtBinary.bin'_of_nat.simps
      append_eq_conv_conj bin'_times_pow4 group_2_flatten_id nat_of_bin_via_bin'
      power_Suc rev_swap set_all_length_2_wf)

lemma take_bin'_minus [simp]: "starts_with_True b \<Longrightarrow> set b \<subseteq> {w. length w = 2} \<Longrightarrow>
       take (length b - k) (bin'_of_nat (nat_of_bin' b * 4^l)) =
       take (length b - k) b"
  apply (induction l)
   apply auto
  using ExtBinary.bin'_nat_bin' set_all_length_2_wf apply force
proof -
  fix la :: nat
  assume a1: "take (length b - k) (group_2 False (rev (bin_of_nat
              ((rev (flatten b))\<^sub>2 * 4 ^ la)))) = take (length b - k) b"
  assume a2: "starts_with_True b"
  assume "set b \<subseteq> {w. length w = 2}"
  then have "\<forall>n. b @ [False, False] \<up> n = ExtBinary.bin'_of_bin (bin_of_nat
             (ExtBinary.nat_of_bin' b * 4 ^ n))"
    using a2 ExtBinary.bin'_of_nat.simps bin'_times_pow4 by presburger
  then show "take (length b - k) (group_2 False (rev (bin_of_nat ((rev (flatten b))\<^sub>2 *
             (4 * 4 ^ la))))) = take (length b - k) b"
    using a1 by (metis (no_types) ExtBinary.bin'_of_bin.elims
        ExtBinary.bin'_of_nat.simps ExtBinary.bin_of_bin'.elims ExtBinary.nat_bin'_nat
        ExtBinary.nat_of_bin'.simps append_eq_conv_conj bin_nat_bin_drop_zs
        diff_le_self nat_of_bin_via_bin' power_Suc take_ge_eq)
qed

lemma length_bin'_pow_add [simp]: "starts_with_True b \<Longrightarrow> bin'_wf b \<Longrightarrow> l < 4^k \<Longrightarrow>
       length (bin'_of_nat ((nat_of_bin' b) * 4^k + l)) = length b + k"
proof (induction k arbitrary: l)
  case 0
  hence 1: "l = 0" by simp
  have 2: "ends_in True (rev (flatten b)) \<or> ends_in True (rev (tl (flatten b)))"
    using 0(1, 2) apply (induction b rule: starts_with_True_induct)
    by fastforce+
  show ?case apply (simp add: 1) using 2
    by (metis "0.prems"(1) "0.prems"(2) ExtBinary.bin'_nat_bin'
        ExtBinary.bin'_nat_bin'_drop_zs bin_nat_bin_drop_zs length_group_2 length_rev
        rev_rev_ident)
next
  case (Suc k)
  then show ?case apply simp
    by (smt (verit, del_insts) ExtBinary.bin'_of_bin.simps
        ExtBinary.bin'_of_nat.simps ExtBinary.bin_of_bin'.simps
        ExtBinary.nat_of_bin'.simps Suc(2) Suc(3) Suc_eq_plus1 add.commute
        add_Suc_right add_Suc_shift bin'_times_pow4 bin_nat_bin_drop_zs length_Cons
        length_append length_append length_group_2 length_replicate length_rev
        mult.left_commute nat_bin_nat nat_of_bin'_gt_0_start_True nat_of_bin_trim
        power_Suc set_all_length_2_wf suffix'_len_eq)
qed

lemma length_without_add_eq' [simp]: "starts_with_True b \<Longrightarrow> bin'_wf b \<Longrightarrow> l < 4^k \<Longrightarrow>
       length (bin'_of_nat ((nat_of_bin' b) * 4^k + l)) =
       length (bin'_of_nat ((nat_of_bin' b) * 4^k))"
  using nat_of_bin'_gt_0_start_True suffix'_len_eq by blast

lemma take_higher_bin' [simp]: "starts_with_True b \<Longrightarrow> set b \<subseteq> {w. length w = 2} \<Longrightarrow>
      l < 4^k \<Longrightarrow> take (length b) (bin'_of_nat (nat_of_bin' b * 4^k + l)) = b"
  by (metis ExtBinary.nat_bin'_nat drop_suffix'_bin')

lemma length_bin_of_nat_mod: "k \<le> length w \<Longrightarrow>
       length (bin_of_nat ((w @ [True])\<^sub>2 - (w @ [True])\<^sub>2 mod 2 ^ k)) =
       length (w @ [True])"
proof -
  assume a1: "k \<le> length w"
  have 1: "(w @ [True])\<^sub>2 div 2 ^ k > 0" using a1
    by (metis Euclidean_Rings.div_eq_0_iff bin_nat_bin bot_nat_0.not_eq_extremum
        length_append_singleton length_bin_of_nat_le_iff nat_zero_less_power_iff
        not_less_eq_eq pos2)
  have 2: "(w @ [True])\<^sub>2 mod 2 ^ k < 2 ^ k" by simp
  have 3: "(w @ [True])\<^sub>2 div 2 ^ k * 2 ^ k + (w @ [True])\<^sub>2 mod 2 ^ k = (w @ [True])\<^sub>2"
    by (rule div_mult_mod_eq)
  note 4 = suffix_len_eq [OF 1 2, unfolded 3]
  show ?thesis using 4 by (simp add: minus_mod_eq_mult_div mult.commute)
qed

lemma adj_sq'_same_length:
  assumes len: "length w \<ge> 7" \<comment> \<open>lower bound for \<open>4 + l div 2 < l\<close>\<close>
  and w_subset: "set w \<subseteq> {w. length w = 2}"
  and s2Tw: "starts_with [True, False] w"
  defines k: "k \<equiv> suffix'_len w"
  defines w': "w' \<equiv> adj_sq\<^sub>w' w"
  shows "length w' = length w"
proof -
  define n where n: "n = gn' w"
  define w\<^sub>n where wn_def: "w\<^sub>n = bin'_of_nat n"
  have "n > 0" unfolding n by (rule gn'_gt_0)
  define ps where ps: "ps \<equiv> take (length w\<^sub>n - k) w\<^sub>n"
  define up where up: "up = nat_of_bin' ps"
  define lo where lo: "lo = n mod 4^k"
  define n' where n': "n' = n - lo"
  have sTw: "starts_with_True w" using s2Tw by auto
  have k_gt_0: "k > 0" using len unfolding k suffix'_len_def by simp
  let ?lo = "bin'_of_nat lo" and ?up = "bin'_of_nat up"
  have w_wf: "bin'_wf w" apply standard
    using w_subset set_all_length_2_wf by auto
  from len have "k < length w" unfolding k unfolding suffix'_len_def by simp
  hence "k \<le> length w" by simp
  from \<open>k < length w\<close> have "up > 0" unfolding up ps wn_def n using w_wf k_gt_0
    apply (cases "starts_with_True w")
    unfolding starts_with_True_gn'_eq_gn apply simp
  proof -
    assume a1: "k < length w" and a2: "bin'_wf w" and a3: "0 < k"
    show "0 < (rev (flatten
          (take (Suc (length (dropWhile Not (flatten w)) div 2) - k)
          (group_2 False (True # dropWhile Not (flatten w))))))\<^sub>2"
    proof -
      from sTw obtain h :: "bool list" and t :: bin' where w_def: "w = h#t"
        by (rule starts_with_True.elims(2))
      have 1: "bin'_wf t" using a2 unfolding w_def by (rule bin'_wf_ConsD)
      have 2: "h = [True, True] \<or> h = [True, False] \<or> h = [False, True]"
        using a2 sTw unfolding w_def by fastforce
      have 3: "k \<le> length w" using a1 by simp
      have "True \<in> set (flatten
            (take (Suc (length (dropWhile Not (flatten w)) div 2) - k)
            (group_2 False (True # dropWhile Not (flatten w)))))"
        unfolding w_def using 1 2 apply auto
          apply (smt (z3) 3 append_Cons append_take_drop_id bin'_wf_even
            diff_is_0_eq even_Suc even_group_2_Cons1 length_Cons list.set_intros(1)
            nat_of_bin'_gt_0_iff nat_of_bin'_gt_0_start_True not_less_eq_eq
            rev.simps(2) rev_singleton_conv set_rev starts_with_True.simps(2)
            starts_with_True_app take_eq_Nil w_def)
         apply (smt (z3) 3 append_Cons append_take_drop_id bin'_wf_even diff_is_0_eq
            even_Suc even_group_2_Cons1 length_Cons list.set_intros(1)
            nat_of_bin'_gt_0_iff nat_of_bin'_gt_0_start_True not_less_eq_eq
            rev.simps(2) rev_singleton_conv set_rev starts_with_True.simps(2)
            starts_with_True_app take_eq_Nil w_def)
        by (metis Suc_le_eq a1 append_take_drop_id bin'_wf_even diff_is_0_eq
            even_group_2_Cons2 length_Cons list.set_intros(1) nat_of_bin'_gt_0_iff
            nat_of_bin'_gt_0_start_True not_less_eq starts_with_True.simps(2)
            starts_with_True_app take_eq_Nil w_def)
      thus "0 < (rev (flatten
            (take (Suc (length (dropWhile Not (flatten w)) div 2) - k)
            (group_2 False (True # dropWhile Not (flatten w))))))\<^sub>2"
        by (simp add: nat_of_bin_gt_0_iff)
    qed
    show "\<not> starts_with_True w \<Longrightarrow> 0 < ExtBinary.nat_of_bin'
          (take (length (ExtBinary.bin'_of_nat (Goedel_Numbering.gn' w)) - k)
          (ExtBinary.bin'_of_nat (Goedel_Numbering.gn' w)))"
      using sTw by contradiction
  qed
  have lo_lt_pow4k: "lo < 4 ^ k" unfolding lo using zero_less_power pos2 by simp
  then have "length (bin'_of_nat lo) \<le> k"
    using length_bin'_of_nat_le_iff by blast

  have "starts_with_True w\<^sub>n" unfolding wn_def using \<open>0 < n\<close> by blast
  moreover from \<open>k \<le> length w\<close> have "k < length w\<^sub>n"
    unfolding wn_def n
    using \<open>k < length w\<close> length_gn'_ge order_less_le_trans sTw w_wf by blast
  ultimately have "starts_with_True ps" unfolding ps
    by (metis append_take_drop_id diff_is_0_eq leD starts_with_True_app take_eq_Nil)
  have 1: "n - n mod 4 ^ k = (n div (4 ^ k)) * 4 ^ k" by (rule minus_mod_eq_div_mult)
  have n'_split: "n' = up * 4^k" unfolding up wn_def ps n' lo 1
  proof (induction k)
    case 0
    then show ?case using nat_of_bin_trim by auto
  next
    case (Suc k)
    hence 1: "n div 4 ^ k = nat_of_bin' (take (length (bin'_of_nat n) - k)
              (bin'_of_nat n))" by simp
    have 2: "\<And>n::nat. n div 4 = n div 2 div 2" by simp
    have "n div 4 ^ k div 4 = nat_of_bin'
          (butlast (take (length (bin'_of_nat n) - k) (bin'_of_nat n)))"
      unfolding 1 apply simp unfolding 2 nat_of_bin_div2'
      apply (rule flatten_butlast_bin' [THEN ssubst])
       apply (rule bin'_wf_takeI)
       apply blast
      by (metis rev_butlast_is_tl_rev)
    hence "n div 4 ^ k div 4 = nat_of_bin'
          (take (length (bin'_of_nat n) - (Suc k)) (bin'_of_nat n))"
      apply (rule ssubst)
      by (metis Suc_eq_plus1 butlast_take diff_diff_left diff_le_self)
    hence "n div 4 ^ (Suc k) = nat_of_bin'
          (take (length (bin'_of_nat n) - (Suc k)) (bin'_of_nat n))"
      by (metis div_mult2_eq power_Suc2)
    then show ?case by simp
  qed
  have n_split: "n = up * 4^k + lo" by (fold n'_split, unfold lo n', simp)

  have l_eq: "length (bin'_of_nat n) = length (bin'_of_nat n')"
    unfolding n_split n'_split using \<open>up > 0\<close> \<open>lo < 4 ^ k\<close> by (rule suffix'_len_eq)

  define sq where sq: "sq = adj_square' n"
  define sq_diff where "sq_diff = sq - n'"
  have sq_w': "bin'_of_nat sq = bin'_of_nat (gn' w')" unfolding w' adj_sq\<^sub>w'_def sq n
    gn'_def apply simp
  proof (induction w rule: bij_bin'_bin.induct)
    case 1
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (2 t)
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (3 t)
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (4 b t)
    then show ?case apply auto
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)+
  next
    case (5 t)
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (6 t)
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (7 t)
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (8 b1 b2 b3 t' t)
    then show ?case apply auto
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)+
  qed
  have sq_eq: "sq = next_square n'" unfolding sq adj_square_def
    unfolding n' lo k n using adj_square'_def gn'_inv_id w_wf by presburger
  have sq_split: "sq = up * 4^k + sq_diff" unfolding sq_diff_def n'_split[symmetric] sq_eq
    using next_sq_correct2[of n'] by (subst add_diff_inverse_nat) (elim leD, blast)
  have "sq_diff < 2 ^ (4 + (bit_length n' - 1) div 2)" unfolding sq_diff_def sq_eq suffix_len_def
    using next_sq_diff .
  also have "... \<le> 4 ^ k" unfolding l_eq[symmetric] n k suffix'_len_def
  proof simp
    have 1: "(2::nat) ^ (4 + k) = 16 * 2 ^ k" for k :: nat by (simp add: power_add)
    have 2: "(4::nat) ^ (3 + k) = 64 * 4 ^ k" for k :: nat by (simp add: power_add)
    have 3: "2 * k \<le> length (bij_bin'_bin w)"
      using \<open>k < length w\<close> length_bij_bin'_bin_lower_bound [OF sTw w_wf] by simp
    have 4: "(2::nat) ^ (2 * k) = 4 ^ k"
      by (metis numeral_Bit0_eq_double power2_eq_square power_mult)
    have 5: "(2::nat) ^ (length w) \<le> 4 * 4 ^ (length w div 2)"
      apply (cases "even (length w)")
      apply (smt (verit) div_le_dividend dvd_mult_div_cancel even_Suc even_Suc_div_two
          nonzero_mult_div_cancel_left numeral_1_eq_Suc_0 numeral_2_eq_2
          numeral_Bit0_eq_double odd_Suc_div_two power2_eq_square power_mult)
      by (smt (verit, ccfv_threshold) One_nat_def bot_nat_0.not_eq_extremum
          div_le_dividend dvd_mult_div_cancel even_Suc nat_zero_less_power_iff
          nonzero_mult_div_cancel_left numeral_1_eq_Suc_0 numeral_Bit0_eq_double
          odd_Suc_div_two plus_1_eq_Suc pos2 power2_eq_square power_add power_mult)
    have "(2::nat) ^ ((length (bin_of_nat n') - Suc 0) div 2) \<le>
          4 * 4 ^ (length w div 2)" unfolding n' n lo gn'_def gn_def
      unfolding length_bin_of_nat_mod [OF 3, unfolded 4] apply simp
      using length_bij_bin'_bin_upper_bound [OF w_wf] 5
      by (smt (verit, best) div_le_mono le_trans length_bin_of_nat_le_iff
          nonzero_mult_div_cancel_left verit_comp_simplify1(3) zero_neq_numeral)
    thus "(2::nat) ^ (4 + (length (bin_of_nat n') - Suc 0) div 2) \<le>
          4 ^ (3 + length w div 2)" unfolding 1 2 by simp
  qed
  finally have sq_diff_lt_pow4k: "sq_diff < 4 ^ k" .

  from adj_sq_gt_0 have *: "bit_length (adj_square x) \<ge> 1" for x
    unfolding One_nat_def by (intro Suc_leI) fast

  have "length w + 1 = length w\<^sub>n" unfolding wn_def n apply simp
    unfolding gn'_def gn_def apply simp
    using length_bij_bin'_bin_starts_with_TrueX [OF s2Tw w_wf] by simp
  also have "... = length (bin'_of_nat n)" unfolding wn_def ..
  also have "... = length (bin'_of_nat n')" by (rule l_eq)
  also have "... = length (bin'_of_nat sq)" unfolding n'_split sq_split
    using \<open>up > 0\<close> \<open>sq_diff < 4 ^ k\<close> by (rule suffix'_len_eq[symmetric])
  also have "... = length w' + 1" unfolding w' sq n
    using s2Tw len w_wf
  proof (induction w rule: bij_bin'_bin.induct)
    case 1
    then show ?case by simp
  next
    case (2 t)
    then show ?case by simp
  next
    case (3 t)
    then show ?case by simp
  next
    case (4 b t)
    then show ?case by simp
  next
    case (5 t)
    have t_wf: "bin'_wf t" using 5(3) by fastforce
    hence [simp]: "length (flatten t) = 2 * length t" by simp
    have 1: "6 \<le> length t" using 5 by simp
    have 2: "12 \<le> length (flatten t)" using 5(3) [THEN bin'_wf_ConsD] 1 by simp
    have 3: "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2 \<le>
             (replicate (2 * length t + 3) True)\<^sub>2"
    proof -
      have 3: "butlast (rev (flatten t) @ [False, True, True]) =
               rev (flatten t) @ [False, True]" by (simp add: butlast_append)
      have 4: "bij_bin_bin' (rev (flatten t) @ [False, True]) =
               bin'_of_bin (rev (flatten t) @ [False, True])"
        by (smt (verit, best) Nil_is_rev_conv append.assoc append1_eq_conv
            append_Cons bij_bin_bin'.elims rev.simps(2) rev_singleton_conv)
      have 6: "group_2 False (True # False # flatten t) =
               [True, False]#t" using t_wf by (simp add: even_group_2_Cons2)
      note 7 = gn'_inv_def [of "(rev (flatten t) @ [False, True, True])\<^sub>2",
          unfolded gn_inv_def, simplified, unfolded 3 4, simplified, unfolded 5]
      have 8: "(4::nat) ^ (3 + length ([True, False] # t) div 2) =
               2 ^ (6 + length ([True, False] # t) div 2 * 2)" apply simp
        by (metis (no_types, lifting) mult_2_right numeral_Bit0 power_add
            power_mult_distrib)
      have 9: "length (rev (flatten t) @ [False, True, True]) >
               6 + length ([True, False] # t) div 2 * 2" using 1 by simp
      have 10: "(rev (flatten t) @ [False, True, True])\<^sub>2 \<ge>
                4 ^ (3 + length ([True, False] # t) div 2)" unfolding 8
        using length_bin_of_nat_le_iff [of "(rev (flatten t) @ [False, True, True])\<^sub>2"
            "6 + length ([True, False] # t) div 2 * 2"] 9 by simp
      have 11: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 =
                (replicate (2 * length t) False @ [True])\<^sub>2"
        unfolding bin_app_sub_same_prefix by simp
      also have "... = 2 ^ (2 * length t)" by (simp add: nat_of_bin_append1)
      finally have 12: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                        (rev (flatten t) @ [False, True, True])\<^sub>2 =
                        2 ^ (2 * length t)" .
      have 13: "6 + 2 * (Suc (length t) div 2) - 2 * length t = 0" using 1 apply simp
        using nat_le_linear nle_le by fastforce
      have 14: "length (False \<up> (6 + 2 * (Suc (length t) div 2)) @
                drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t))) \<ge>
                2 * length t"
        using 1 by simp
      have 15: "(rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2) \<ge>
                ((replicate (2 * length t) False) @ [False, True, True])\<^sub>2"
        unfolding nmn_mod_pow4m_nat_of_bin apply simp
        unfolding 13 apply simp
        apply (subst append_assoc [symmetric])
        apply (rule nat_of_bin_app_le)
         apply auto
        using 13 diff_is_0_eq le_add_diff_inverse by blast
      note 16 = nmn_mod_pow4m_nat_of_bin
        [of "(rev (flatten t) @ [False, True, True])\<^sub>2"
          "(3 + length ([True, False] # t) div 2)", simplified,
          unfolded nat_of_bin_app_0s]
      have 17: "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2 -
                ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2)) <
                2 ^ (6 + 2 * (Suc (length t) div 2))" unfolding adj_square'_def
      proof (simp del: next_sq_def)
        have 17: "(rev (flatten t) @ [False, True, True])\<^sub>2 -
              (rev (flatten t) @ [False, True, True])\<^sub>2 mod
              4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2) =
              (drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t)) @
              drop (6 + 2 * (Suc (length t) div 2) - 2 * length t)
              [False, True, True])\<^sub>2 * 2 ^ (6 + 2 * (Suc (length t) div 2))"
          unfolding 16 [symmetric] by (simp add: 7 suffix'_len_def)
        have 18: "(drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t)) @
                  [False, True, True])\<^sub>2 * 2 ^ (6 + 2 * (Suc (length t) div 2)) +
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  2 ^ (6 + Suc (length t) div 2 * 2) =
                  (rev (flatten t) @ [False, True, True])\<^sub>2"
          by (metis 13 16 8 add.commute drop0 le_add_diff_inverse length_Cons
              mod_less_eq_dividend)
        have 19: "next_square ((drop (6 + 2 * (Suc (length t) div 2))
                  (rev (flatten t)) @ [False, True, True])\<^sub>2 *
                  2 ^ (6 + 2 * (Suc (length t) div 2))) +
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  2 ^ (6 + Suc (length t) div 2 * 2)
                  \<ge> (rev (flatten t) @ [False, True, True])\<^sub>2"
          using 18 by (metis diff_add_inverse2 le_diff_conv next_sq_correct2)
        have 20: "4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2) =
                  4 ^ (3 + Suc (length t) div 2)"
          by (simp add: 7 suffix'_len_def)
        have 21: "next_square ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod 4 ^ (3 + Suc (length t)
                  div 2)) - ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod 4 ^ (3 + Suc (length t)
                  div 2)) =
                  next_square ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  4 ^ suffix'_len (gn'_inv (rev (flatten t) @
                  [False, True, True])\<^sub>2)) + (rev (flatten t) @ [False, True, True])\<^sub>2
                  mod 4 ^ (3 + Suc (length t) div 2) -
                  (rev (flatten t) @ [False, True, True])\<^sub>2" by (simp add: 20)
        have 22: "4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2)))
                  div 2 \<le> 6 + 2 * (Suc (length t) div 2)" by simp
        have 23: "4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  4 ^ (3 + Suc (length t) div 2))) - 1) div 2 \<le>
                  4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2)))
                  div 2" using bit_length_sub
          by (meson diff_le_self div_le_mono nat_add_left_cancel_le
              order_trans_rules(23))
        have 24: "4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  4 ^ (3 + Suc (length t) div 2))) - 1) div 2 \<le>
                  6 + 2 * (Suc (length t) div 2)" using 22 23 by linarith
        show "next_square
              ((rev (flatten t) @ [False, True, True])\<^sub>2 -
              (rev (flatten t) @ [False, True, True])\<^sub>2 mod
              4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2)) +
              (rev (flatten t) @ [False, True, True])\<^sub>2 mod
              4 ^ (3 + Suc (length t) div 2) - (rev (flatten t) @
              [False, True, True])\<^sub>2 < 2 ^ (6 + 2 * (Suc (length t) div 2))"
          using next_sq_diff [of "(rev (flatten t) @ [False, True, True])\<^sub>2 -
      (rev (flatten t) @ [False, True, True])\<^sub>2 mod
      4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2)"]
          unfolding 20 21 using 24 by (meson length_bin_of_nat_le_iff
              order_trans_rules(23))
      qed
      have 18: "(replicate (2 * length t + 3) True)\<^sub>2 = 2 ^ (2 * length t + 3) - Suc 0"
        by simp
      have 19: "take (6 + Suc (length t) div 2 * 2 - 2 * length t)
                [False, True, True] = []" using 1 13 by auto
      have 20: "((2::nat) ^ (6 + 2 * (Suc (length t) div 2))) +
                ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2)) \<le>
                (True \<up> (2 * length t + 3))\<^sub>2" apply simp
        unfolding 8 [simplified] take_mod apply simp
        unfolding 19
      proof simp
        have 1: "(rev (flatten t) @ [False, True, True])\<^sub>2 \<le>
                 2 ^ (2 * length t + 3) - Suc 0" using 1 t_wf
          by (smt (z3) Suc_pred \<open>length (flatten t) = 2 * length t\<close> length_Cons
              length_append length_rev less_Suc_eq_le list.size(3) nat_of_bin_max
              numeral_3_eq_3 pos2 zero_less_power)
        have 2: "(rev (flatten t) @ [True, True, True])\<^sub>2 \<le>
                 2 ^ (2 * length t + 3) - Suc 0"
          by (smt (z3) Suc_pred \<open>length (flatten t) = 2 * length t\<close> length_Cons
              length_append length_rev less_Suc_eq_le list.size(3) nat_of_bin_max
              numeral_3_eq_3 pos2 zero_less_power)
        have 3: "6 + 2 * (Suc (length t) div 2) \<le> 2 * length t"
          using \<open>length t \<ge> 6\<close> by presburger
        have 4: "(2::nat) ^ (6 + 2 * (Suc (length t) div 2)) -
                 (take (6 + Suc (length t) div 2 * 2) (rev (flatten t)))\<^sub>2 \<le>
                 2 ^ (2 * length t)" using 3
          by (meson le_diff_conv log2.valid_base power_increasing_iff trans_le_add1)
        have 5: "2 ^ (2 * length t) = (False \<up> (2 * length t) @ [True])\<^sub>2"
          by (rule sym) fact
        show "2 ^ (6 + 2 * (Suc (length t) div 2)) +
              (rev (flatten t) @ [False, True, True])\<^sub>2 -
              (take (6 + Suc (length t) div 2 * 2) (rev (flatten t)))\<^sub>2
              \<le> 2 ^ (2 * length t + 3) - Suc 0" using 1 2 4 5 11 by linarith
      qed
      show "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2
            \<le> (True \<up> (2 * length t + 3))\<^sub>2" using 17 20 by linarith
    qed
    have 4: "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2 \<ge>
             ((replicate (2 * length t) False) @ [False, True, True])\<^sub>2"
    proof -
      have 3: "butlast (rev (flatten t) @ [False, True, True]) =
               rev (flatten t) @ [False, True]" by (simp add: butlast_append)
      have 4: "bij_bin_bin' (rev (flatten t) @ [False, True]) =
               bin'_of_bin (rev (flatten t) @ [False, True])"
        by (smt (verit, best) Nil_is_rev_conv append.assoc append1_eq_conv
            append_Cons bij_bin_bin'.elims rev.simps(2) rev_singleton_conv)
      have 6: "group_2 False (True # False # flatten t) =
               [True, False]#t" using t_wf by (simp add: even_group_2_Cons2)
      note 7 = gn'_inv_def [of "(rev (flatten t) @ [False, True, True])\<^sub>2",
          unfolded gn_inv_def, simplified, unfolded 3 4, simplified, unfolded 5]
      have 8: "(4::nat) ^ (3 + length ([True, False] # t) div 2) =
               2 ^ (6 + length ([True, False] # t) div 2 * 2)" apply simp
        by (metis (no_types, lifting) mult_2_right numeral_Bit0 power_add
            power_mult_distrib)
      have 9: "length (rev (flatten t) @ [False, True, True]) >
               6 + length ([True, False] # t) div 2 * 2" using 1 by simp
      have 10: "(rev (flatten t) @ [False, True, True])\<^sub>2 \<ge>
                4 ^ (3 + length ([True, False] # t) div 2)" unfolding 8
        using length_bin_of_nat_le_iff [of "(rev (flatten t) @ [False, True, True])\<^sub>2"
            "6 + length ([True, False] # t) div 2 * 2"] 9 by simp
      have 11: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 =
                (replicate (2 * length t) False @ [True])\<^sub>2"
        unfolding bin_app_sub_same_prefix by simp
      also have "... = 2 ^ (2 * length t)" by (simp add: nat_of_bin_append1)
      finally have 12: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                        (rev (flatten t) @ [False, True, True])\<^sub>2 =
                        2 ^ (2 * length t)" .
      have 13: "6 + 2 * (Suc (length t) div 2) - 2 * length t = 0" using 1 apply simp
        using nat_le_linear nle_le by fastforce
      have 14: "length (False \<up> (6 + 2 * (Suc (length t) div 2)) @
                drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t))) \<ge>
                2 * length t"
        using 1 by simp
      have 15: "(rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2) \<ge>
                ((replicate (2 * length t) False) @ [False, True, True])\<^sub>2"
        unfolding nmn_mod_pow4m_nat_of_bin apply simp
        unfolding 13 apply simp
        apply (subst append_assoc [symmetric])
        apply (rule nat_of_bin_app_le)
         apply auto
        using 13 diff_is_0_eq le_add_diff_inverse by blast
      show "((replicate (2 * length t) False) @ [False, True, True])\<^sub>2
            \<le> adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2" using 15
        unfolding adj_square'_def
        using 6 7 le_trans next_sq_correct2 suffix'_len_def by presburger
    qed
    have 6: "suffix [True, True] ((replicate (2 * length t) False) @ [False, True, True])" by simp
    have 7: "suffix [True, True] (True \<up> (2 * length t + 3))"
      by (metis bin'_repl eval_nat_numeral(3) replicate_Suc replicate_add
          suffix_ConsI suffix_appendI suffix_order.dual_order.refl)
    have 71: "ends_in True (True \<up> (2 * length t + 3))" using 7
      by (metis append_assoc eval_nat_numeral(3) replicate_Suc replicate_add
          replicate_append_same)
    have 8: "\<exists>ys. bin_of_nat (adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2) =
             ys @ [True]"
      using adj_square'_def bin_of_nat_gt_0_end_True next_sq_gt0 by presburger
    have 9: "(bin_of_nat (adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2))\<^sub>2
             \<le> 2 ^ (2 * length t + 3) - Suc 0"
      by (metis 3 One_nat_def nat_bin_nat nat_of_bin_all_True)
    have 10: "(False \<up> (2 * length t) @ [False, True, True])\<^sub>2
              \<le> (bin_of_nat (adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2))\<^sub>2"
      by (simp add: 4)
    note 11 = suffix_bin_of_nat_between [OF 6 7, simplified, OF 71 8 9 10]
    hence 12: "\<exists>x. bin_of_nat (adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2) =
               x @ [True, True]" by (metis append_take_drop_id)
    have 13: "length (rev (flatten t) @ [True, True, True]) =
              length (rev (flatten t) @ [False, True, True])" by simp
    have 14: "ends_in True (replicate (2 * length t + 3) True)" by fact
    have 15: "length (bin_of_nat (adj_square' (rev (flatten t) @
              [False, True, True])\<^sub>2)) =
              length ((replicate (2 * length t) False) @ [False, True, True])"
      apply (rule length_bin_of_nat_between)
           apply simp_all
          apply (fact 14)
      using 8 apply blast
        apply simp
      by fact+
    show ?case using 5 apply auto
      apply (drule bin'_wf_ConsD)
      unfolding gn'_defs gn_defs apply simp
      unfolding 15 apply simp
      apply (rule eT_length_bij_bin_bin' [THEN ssubst])
       apply (metis 12 butlast.simps(2) butlast_append list.simps(3))
      by (simp add: 15)
  next
    case (6 t)
    then show ?case by simp
  next
    case (7 t)
    then show ?case by simp
  next
    case (8 b1 b2 b3 t' t)
    then show ?case by simp
  qed
  finally show l: "length w' = length w" by simp
qed

 (* 
  REMARK: the convention of a TM encoding to start with 1^+0 was here modified to be
  the prefix 101^+0..., so that the prefix "10" is in any case stripped as fixed, and the 
  rest remains variable.
  Doesn't change anything to the argument, since all we need is an infinitude of functionally
  equivalent TMs (of hence unbouded lengths), and it does not matter how the (variably long) 
  prefix is constructed, as long as it is recognizable as such.
  The condition here, however, is required to get the "monotony in terms of word length" for 
  the (new) Gödel numbering (gn')
 *)
lemma adj_sq'_sh_pfx_half:
  assumes len: "length w \<ge> 7" \<comment> \<open>lower bound for \<open>4 + l div 2 < l\<close>\<close>
  and w_subset: "set w \<subseteq> {w. length w = 2}"
  and s2Tw: "starts_with [True, False] w"
  defines k: "k \<equiv> suffix'_len w"
  defines w': "w' \<equiv> adj_sq\<^sub>w' w"
  shows "shared_MSBs' (length w - k) w w'"
proof (intro sh'_msbI)
  define n where n: "n = gn' w"
  define w\<^sub>n where wn_def: "w\<^sub>n = bin'_of_nat n"
  have "n > 0" unfolding n by (rule gn'_gt_0)
  define ps where ps: "ps \<equiv> take (length w\<^sub>n - k) w\<^sub>n"
  define up where up: "up = nat_of_bin' ps"
  define lo where lo: "lo = n mod 4^k"
  define n' where n': "n' = n - lo"
  have sTw: "starts_with_True w" using s2Tw by auto
  have k_gt_0: "k > 0" using len unfolding k suffix'_len_def by simp
  let ?lo = "bin'_of_nat lo" and ?up = "bin'_of_nat up"
  have w_wf: "bin'_wf w" apply standard
    using w_subset set_all_length_2_wf by auto
  from len have "k < length w" unfolding k unfolding suffix'_len_def by simp
  hence "k \<le> length w" by simp
  from \<open>k < length w\<close> have "up > 0" unfolding up ps wn_def n using w_wf k_gt_0
    apply (cases "starts_with_True w")
    unfolding starts_with_True_gn'_eq_gn apply simp
  proof -
    assume a1: "k < length w" and a2: "bin'_wf w" and a3: "0 < k"
    show "0 < (rev (flatten
          (take (Suc (length (dropWhile Not (flatten w)) div 2) - k)
          (group_2 False (True # dropWhile Not (flatten w))))))\<^sub>2"
    proof -
      from sTw obtain h :: "bool list" and t :: bin' where w_def: "w = h#t"
        by (rule starts_with_True.elims(2))
      have 1: "bin'_wf t" using a2 unfolding w_def by (rule bin'_wf_ConsD)
      have 2: "h = [True, True] \<or> h = [True, False] \<or> h = [False, True]"
        using a2 sTw unfolding w_def by fastforce
      have 3: "k \<le> length w" using a1 by simp
      have "True \<in> set (flatten
            (take (Suc (length (dropWhile Not (flatten w)) div 2) - k)
            (group_2 False (True # dropWhile Not (flatten w)))))"
        unfolding w_def using 1 2 apply auto
          apply (smt (z3) 3 append_Cons append_take_drop_id bin'_wf_even
            diff_is_0_eq even_Suc even_group_2_Cons1 length_Cons list.set_intros(1)
            nat_of_bin'_gt_0_iff nat_of_bin'_gt_0_start_True not_less_eq_eq
            rev.simps(2) rev_singleton_conv set_rev starts_with_True.simps(2)
            starts_with_True_app take_eq_Nil w_def)
         apply (smt (z3) 3 append_Cons append_take_drop_id bin'_wf_even diff_is_0_eq
            even_Suc even_group_2_Cons1 length_Cons list.set_intros(1)
            nat_of_bin'_gt_0_iff nat_of_bin'_gt_0_start_True not_less_eq_eq
            rev.simps(2) rev_singleton_conv set_rev starts_with_True.simps(2)
            starts_with_True_app take_eq_Nil w_def)
        by (metis Suc_le_eq a1 append_take_drop_id bin'_wf_even diff_is_0_eq
            even_group_2_Cons2 length_Cons list.set_intros(1) nat_of_bin'_gt_0_iff
            nat_of_bin'_gt_0_start_True not_less_eq starts_with_True.simps(2)
            starts_with_True_app take_eq_Nil w_def)
      thus "0 < (rev (flatten
            (take (Suc (length (dropWhile Not (flatten w)) div 2) - k)
            (group_2 False (True # dropWhile Not (flatten w))))))\<^sub>2"
        by (simp add: nat_of_bin_gt_0_iff)
    qed
    show "\<not> starts_with_True w \<Longrightarrow> 0 < ExtBinary.nat_of_bin'
          (take (length (ExtBinary.bin'_of_nat (Goedel_Numbering.gn' w)) - k)
          (ExtBinary.bin'_of_nat (Goedel_Numbering.gn' w)))"
      using sTw by contradiction
  qed
  have lo_lt_pow4k: "lo < 4 ^ k" unfolding lo using zero_less_power pos2 by simp
  then have "length (bin'_of_nat lo) \<le> k"
    using length_bin'_of_nat_le_iff by blast

  have "starts_with_True w\<^sub>n" unfolding wn_def using \<open>0 < n\<close> by blast
  moreover from \<open>k \<le> length w\<close> have "k < length w\<^sub>n"
    unfolding wn_def n
    using \<open>k < length w\<close> length_gn'_ge order_less_le_trans sTw w_wf by blast
  ultimately have "starts_with_True ps" unfolding ps
    by (metis append_take_drop_id diff_is_0_eq leD starts_with_True_app take_eq_Nil)
  have 1: "n - n mod 4 ^ k = (n div (4 ^ k)) * 4 ^ k" by (rule minus_mod_eq_div_mult)
  have n'_split: "n' = up * 4^k" unfolding up wn_def ps n' lo 1
  proof (induction k)
    case 0
    then show ?case using nat_of_bin_trim by auto
  next
    case (Suc k)
    hence 1: "n div 4 ^ k = nat_of_bin' (take (length (bin'_of_nat n) - k)
              (bin'_of_nat n))" by simp
    have 2: "\<And>n::nat. n div 4 = n div 2 div 2" by simp
    have "n div 4 ^ k div 4 = nat_of_bin'
          (butlast (take (length (bin'_of_nat n) - k) (bin'_of_nat n)))"
      unfolding 1 apply simp unfolding 2 nat_of_bin_div2'
      apply (rule flatten_butlast_bin' [THEN ssubst])
       apply (rule bin'_wf_takeI)
       apply blast
      by (metis rev_butlast_is_tl_rev)
    hence "n div 4 ^ k div 4 = nat_of_bin'
          (take (length (bin'_of_nat n) - (Suc k)) (bin'_of_nat n))"
      apply (rule ssubst)
      by (metis Suc_eq_plus1 butlast_take diff_diff_left diff_le_self)
    hence "n div 4 ^ (Suc k) = nat_of_bin'
          (take (length (bin'_of_nat n) - (Suc k)) (bin'_of_nat n))"
      by (metis div_mult2_eq power_Suc2)
    then show ?case by simp
  qed
  have n_split: "n = up * 4^k + lo" by (fold n'_split, unfold lo n', simp)

  have l_eq: "length (bin'_of_nat n) = length (bin'_of_nat n')"
    unfolding n_split n'_split using \<open>up > 0\<close> \<open>lo < 4 ^ k\<close> by (rule suffix'_len_eq)

  define sq where sq: "sq = adj_square' n"
  define sq_diff where "sq_diff = sq - n'"
  have sq_w': "bin'_of_nat sq = bin'_of_nat (gn' w')" unfolding w' adj_sq\<^sub>w'_def sq n
    gn'_def apply simp
  proof (induction w rule: bij_bin'_bin.induct)
    case 1
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (2 t)
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (3 t)
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (4 b t)
    then show ?case apply auto
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)+
  next
    case (5 t)
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (6 t)
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (7 t)
    then show ?case apply simp
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)
  next
    case (8 b1 b2 b3 t' t)
    then show ?case apply auto
      by (metis adj_square'_def bij_bin'_bin_bin' gn'_inv_def gn_inv_of_bin
          next_sq_gt0 rev_eq_Cons_iff rev_rev_ident)+
  qed
  have sq_eq: "sq = next_square n'" unfolding sq adj_square_def
    unfolding n' lo k n using adj_square'_def gn'_inv_id w_wf by presburger
  have sq_split: "sq = up * 4^k + sq_diff" unfolding sq_diff_def n'_split[symmetric] sq_eq
    using next_sq_correct2[of n'] by (subst add_diff_inverse_nat) (elim leD, blast)
  have "sq_diff < 2 ^ (4 + (bit_length n' - 1) div 2)" unfolding sq_diff_def sq_eq suffix_len_def
    using next_sq_diff .
  also have "... \<le> 4 ^ k" unfolding l_eq[symmetric] n k suffix'_len_def
  proof simp
    have 1: "(2::nat) ^ (4 + k) = 16 * 2 ^ k" for k :: nat by (simp add: power_add)
    have 2: "(4::nat) ^ (3 + k) = 64 * 4 ^ k" for k :: nat by (simp add: power_add)
    have 3: "2 * k \<le> length (bij_bin'_bin w)"
      using \<open>k < length w\<close> length_bij_bin'_bin_lower_bound [OF sTw w_wf] by simp
    have 4: "(2::nat) ^ (2 * k) = 4 ^ k"
      by (metis numeral_Bit0_eq_double power2_eq_square power_mult)
    have 5: "(2::nat) ^ (length w) \<le> 4 * 4 ^ (length w div 2)"
      apply (cases "even (length w)")
      apply (smt (verit) div_le_dividend dvd_mult_div_cancel even_Suc even_Suc_div_two
          nonzero_mult_div_cancel_left numeral_1_eq_Suc_0 numeral_2_eq_2
          numeral_Bit0_eq_double odd_Suc_div_two power2_eq_square power_mult)
      by (smt (verit, ccfv_threshold) One_nat_def bot_nat_0.not_eq_extremum
          div_le_dividend dvd_mult_div_cancel even_Suc nat_zero_less_power_iff
          nonzero_mult_div_cancel_left numeral_1_eq_Suc_0 numeral_Bit0_eq_double
          odd_Suc_div_two plus_1_eq_Suc pos2 power2_eq_square power_add power_mult)
    have "(2::nat) ^ ((length (bin_of_nat n') - Suc 0) div 2) \<le>
          4 * 4 ^ (length w div 2)" unfolding n' n lo gn'_def gn_def
      unfolding length_bin_of_nat_mod [OF 3, unfolded 4] apply simp
      using length_bij_bin'_bin_upper_bound [OF w_wf] 5
      by (smt (verit, best) div_le_mono le_trans length_bin_of_nat_le_iff
          nonzero_mult_div_cancel_left verit_comp_simplify1(3) zero_neq_numeral)
    thus "(2::nat) ^ (4 + (length (bin_of_nat n') - Suc 0) div 2) \<le>
          4 ^ (3 + length w div 2)" unfolding 1 2 by simp
  qed
  finally have sq_diff_lt_pow4k: "sq_diff < 4 ^ k" .

  from adj_sq_gt_0 have *: "bit_length (adj_square x) \<ge> 1" for x
    unfolding One_nat_def by (intro Suc_leI) fast

  show l: "length w' = length w" unfolding w' by (rule adj_sq'_same_length) fact+

  have lk: "length w - (length w - k) = k" using \<open>length w \<ge> k\<close> by (rule diff_diff_cancel)
  have lwl: "k - length w = 0" using \<open>length w \<ge> k\<close> by simp

  note sq_diff_lt_pow4k
  have sq_diff_nat_bin'_nat: "nat_of_bin' (bin'_of_nat sq_diff) = sq_diff"
    by (rule nat_bin'_nat)
  note lo_lt_pow4k
  note \<open>length ?lo \<le> k\<close>
  have 1: "length (bin'_of_nat (nat_of_bin' ?up * 4 ^ k + nat_of_bin' ?lo)) = length w\<^sub>n"
    using ExtBinary.nat_bin'_nat n_split wn_def by presburger
  have 2: "n' < 4 ^ k \<Longrightarrow> take (length w\<^sub>n - k)
           (bin'_of_nat (nat_of_bin' ?up * 4 ^ k + n')) =
           bin'_of_nat ((nat_of_bin' ?up * 4 ^ k + n') div 4 ^ k)" for n' :: nat
    unfolding 1 [symmetric] nat_bin'_nat
    using take_mk_bin' [of "ExtBinary.bin'_of_nat (up * 4 ^ k + n')" k]
    by (metis ExtBinary.nat_bin'_nat \<open>0 < up\<close> add_is_0 bin'_of_nat_gt_0_start_True
        bin'_of_nat_wf bot_nat_0.not_eq_extremum l_eq mult_is_0 n'_split n_split
        suffix'_len_eq)
  have "w \<noteq> []"
    using sTw starts_with_True.simps(1) by blast
  have 3: "[False, True]#w = w\<^sub>n" unfolding wn_def n gn'_def gn_def
  proof -
    obtain y :: bin' where w_def: "w = [True, False]#y" using assms(3) by auto
    show "[False, True] # w = bin'_of_nat (bij_bin'_bin w @ [True])\<^sub>2"
      unfolding w_def apply simp
      by (metis bin'_wf_ConsD even_group_2_Cons1 even_group_2_Cons2
          flatten_group_2_odd group_2_flatten_id not_Cons_self w_def w_wf)
  qed
  have 4: "take (length ([False, True] # w) - k) ([False, True] # w) =
           [False, True] # take (length w - k) w"
    by (simp add: Suc_diff_le \<open>k \<le> length w\<close>)
  have 5: "take (length w\<^sub>n - k) w\<^sub>n = take (length w\<^sub>n - k)
           (bin'_of_nat (nat_of_bin' ?up * 4 ^ k + nat_of_bin' ?lo))"
    unfolding wn_def n_split nat_bin'_nat ..
  also have "... = take (length w\<^sub>n - k)
        (bin'_of_nat (nat_of_bin' ?up * 4 ^ k + sq_diff))"
    using 2 ExtBinary.nat_bin'_nat lo_lt_pow4k sq_diff_lt_pow4k by auto
  also have "... = take (length w\<^sub>n - k) (bin'_of_nat sq)"
    using ExtBinary.nat_bin'_nat sq_split by presburger
  finally have "take (length w - k) w = take (length w - k) w'" unfolding sq n
      3 [symmetric] 4 w' adj_sq\<^sub>w'_def
  proof -
    assume a1: "[False, True] # take (length w - k) w =
                take (length ([False, True] # w) - k)
                (bin'_of_nat (adj_square' (Goedel_Numbering.gn' w)))"
    have "take (length w - k) w = tl (take (length ([False, True] # w) - k)
          (bin'_of_nat (adj_square' (Goedel_Numbering.gn' w))))" using a1
      by (metis list.sel(3))
    also have "... = take (length w - k)
               (tl (bin'_of_nat (adj_square' (Goedel_Numbering.gn' w))))"
      by (simp add: Suc_diff_le \<open>k \<le> length w\<close> take_tl)
    finally have 1: "take (length w - k)
                     (tl (bin'_of_nat (adj_square' (Goedel_Numbering.gn' w)))) =
                     take (length w - k) w" ..
    have 2: "starts_with [True, False] (tl (bin'_of_nat (adj_square'
             (Goedel_Numbering.gn' w))))"
    proof -
      have 2: "starts_with [True, False] (take (length w - k) w)"
        using assms(3) \<open>length w > k\<close>
        by (metis less_numeral_extra(3) take_Cons' zero_less_diff)
      show "starts_with [True, False] (tl (bin'_of_nat (adj_square'
            (Goedel_Numbering.gn' w))))" using 2 [folded 1, THEN starts_with_takeD] .
    qed
    have 3: "ends_in True (butlast (bin_of_nat (adj_square'
             (Goedel_Numbering.gn' w))))"
      unfolding gn'_def gn_def using assms(1, 3) w_wf
    proof (induction w rule: bij_bin'_bin.induct)
      case 1
      then show ?case by simp
    next
      case (2 t)
      then show ?case by simp
    next
      case (3 t)
      then show ?case by simp
    next
      case (4 b t)
      then show ?case by simp
    next
      case (5 t)
      have t_wf: "bin'_wf t" using 5(3) by fastforce
      hence [simp]: "length (flatten t) = 2 * length t" by simp
      have 1: "length t \<ge> 6" using 5(1) by simp
      have 2: "12 \<le> length (flatten t)" using 5(3) [THEN bin'_wf_ConsD] 1 by simp
    have 3: "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2 \<le>
             (replicate (2 * length t + 3) True)\<^sub>2"
    proof -
      have 3: "butlast (rev (flatten t) @ [False, True, True]) =
               rev (flatten t) @ [False, True]" by (simp add: butlast_append)
      have 4: "bij_bin_bin' (rev (flatten t) @ [False, True]) =
               bin'_of_bin (rev (flatten t) @ [False, True])"
        by (smt (verit, best) Nil_is_rev_conv append.assoc append1_eq_conv
            append_Cons bij_bin_bin'.elims rev.simps(2) rev_singleton_conv)
      have 6: "group_2 False (True # False # flatten t) =
               [True, False]#t" using t_wf by (simp add: even_group_2_Cons2)
      note 7 = gn'_inv_def [of "(rev (flatten t) @ [False, True, True])\<^sub>2",
          unfolded gn_inv_def, simplified, unfolded 3 4, simplified, unfolded 5]
      have 8: "(4::nat) ^ (3 + length ([True, False] # t) div 2) =
               2 ^ (6 + length ([True, False] # t) div 2 * 2)" apply simp
        by (metis (no_types, lifting) mult_2_right numeral_Bit0 power_add
            power_mult_distrib)
      have 9: "length (rev (flatten t) @ [False, True, True]) >
               6 + length ([True, False] # t) div 2 * 2" using 1 by simp
      have 10: "(rev (flatten t) @ [False, True, True])\<^sub>2 \<ge>
                4 ^ (3 + length ([True, False] # t) div 2)" unfolding 8
        using length_bin_of_nat_le_iff [of "(rev (flatten t) @ [False, True, True])\<^sub>2"
            "6 + length ([True, False] # t) div 2 * 2"] 9 by simp
      have 11: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 =
                (replicate (2 * length t) False @ [True])\<^sub>2"
        unfolding bin_app_sub_same_prefix by simp
      also have "... = 2 ^ (2 * length t)" by (simp add: nat_of_bin_append1)
      finally have 12: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                        (rev (flatten t) @ [False, True, True])\<^sub>2 =
                        2 ^ (2 * length t)" .
      have 13: "6 + 2 * (Suc (length t) div 2) - 2 * length t = 0" using 1 apply simp
        using nat_le_linear nle_le by fastforce
      have 14: "length (False \<up> (6 + 2 * (Suc (length t) div 2)) @
                drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t))) \<ge>
                2 * length t"
        using 1 by simp
      have 15: "(rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2) \<ge>
                ((replicate (2 * length t) False) @ [False, True, True])\<^sub>2"
        unfolding nmn_mod_pow4m_nat_of_bin apply simp
        unfolding 13 apply simp
        apply (subst append_assoc [symmetric])
        apply (rule nat_of_bin_app_le)
         apply auto
        using 13 diff_is_0_eq le_add_diff_inverse by blast
      note 16 = nmn_mod_pow4m_nat_of_bin
        [of "(rev (flatten t) @ [False, True, True])\<^sub>2"
          "(3 + length ([True, False] # t) div 2)", simplified,
          unfolded nat_of_bin_app_0s]
      have 17: "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2 -
                ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2)) <
                2 ^ (6 + 2 * (Suc (length t) div 2))" unfolding adj_square'_def
      proof (simp del: next_sq_def)
        have 17: "(rev (flatten t) @ [False, True, True])\<^sub>2 -
              (rev (flatten t) @ [False, True, True])\<^sub>2 mod
              4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2) =
              (drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t)) @
              drop (6 + 2 * (Suc (length t) div 2) - 2 * length t)
              [False, True, True])\<^sub>2 * 2 ^ (6 + 2 * (Suc (length t) div 2))"
          unfolding 16 [symmetric] by (simp add: 7 suffix'_len_def)
        have 18: "(drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t)) @
                  [False, True, True])\<^sub>2 * 2 ^ (6 + 2 * (Suc (length t) div 2)) +
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  2 ^ (6 + Suc (length t) div 2 * 2) =
                  (rev (flatten t) @ [False, True, True])\<^sub>2"
          by (metis 13 16 8 add.commute drop0 le_add_diff_inverse length_Cons
              mod_less_eq_dividend)
        have 19: "next_square ((drop (6 + 2 * (Suc (length t) div 2))
                  (rev (flatten t)) @ [False, True, True])\<^sub>2 *
                  2 ^ (6 + 2 * (Suc (length t) div 2))) +
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  2 ^ (6 + Suc (length t) div 2 * 2)
                  \<ge> (rev (flatten t) @ [False, True, True])\<^sub>2"
          using 18 by (metis diff_add_inverse2 le_diff_conv next_sq_correct2)
        have 20: "4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2) =
                  4 ^ (3 + Suc (length t) div 2)"
          by (simp add: 7 suffix'_len_def)
        have 21: "next_square ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod 4 ^ (3 + Suc (length t)
                  div 2)) - ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod 4 ^ (3 + Suc (length t)
                  div 2)) =
                  next_square ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  4 ^ suffix'_len (gn'_inv (rev (flatten t) @
                  [False, True, True])\<^sub>2)) + (rev (flatten t) @ [False, True, True])\<^sub>2
                  mod 4 ^ (3 + Suc (length t) div 2) -
                  (rev (flatten t) @ [False, True, True])\<^sub>2" by (simp add: 20)
        have 22: "4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2)))
                  div 2 \<le> 6 + 2 * (Suc (length t) div 2)" by simp
        have 23: "4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  4 ^ (3 + Suc (length t) div 2))) - 1) div 2 \<le>
                  4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2)))
                  div 2" using bit_length_sub
          by (meson diff_le_self div_le_mono nat_add_left_cancel_le
              order_trans_rules(23))
        have 24: "4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  4 ^ (3 + Suc (length t) div 2))) - 1) div 2 \<le>
                  6 + 2 * (Suc (length t) div 2)" using 22 23 by linarith
        show "next_square
              ((rev (flatten t) @ [False, True, True])\<^sub>2 -
              (rev (flatten t) @ [False, True, True])\<^sub>2 mod
              4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2)) +
              (rev (flatten t) @ [False, True, True])\<^sub>2 mod
              4 ^ (3 + Suc (length t) div 2) - (rev (flatten t) @
              [False, True, True])\<^sub>2 < 2 ^ (6 + 2 * (Suc (length t) div 2))"
          using next_sq_diff [of "(rev (flatten t) @ [False, True, True])\<^sub>2 -
      (rev (flatten t) @ [False, True, True])\<^sub>2 mod
      4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2)"]
          unfolding 20 21 using 24 by (meson length_bin_of_nat_le_iff
              order_trans_rules(23))
      qed
      have 18: "(replicate (2 * length t + 3) True)\<^sub>2 = 2 ^ (2 * length t + 3) - Suc 0"
        by simp
      have 19: "take (6 + Suc (length t) div 2 * 2 - 2 * length t)
                [False, True, True] = []" using 1 13 by auto
      have 20: "((2::nat) ^ (6 + 2 * (Suc (length t) div 2))) +
                ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2)) \<le>
                (True \<up> (2 * length t + 3))\<^sub>2" apply simp
        unfolding 8 [simplified] take_mod apply simp
        unfolding 19
      proof simp
        have 1: "(rev (flatten t) @ [False, True, True])\<^sub>2 \<le>
                 2 ^ (2 * length t + 3) - Suc 0" using 1 t_wf
          by (smt (z3) Suc_pred \<open>length (flatten t) = 2 * length t\<close> length_Cons
              length_append length_rev less_Suc_eq_le list.size(3) nat_of_bin_max
              numeral_3_eq_3 pos2 zero_less_power)
        have 2: "(rev (flatten t) @ [True, True, True])\<^sub>2 \<le>
                 2 ^ (2 * length t + 3) - Suc 0"
          by (smt (z3) Suc_pred \<open>length (flatten t) = 2 * length t\<close> length_Cons
              length_append length_rev less_Suc_eq_le list.size(3) nat_of_bin_max
              numeral_3_eq_3 pos2 zero_less_power)
        have 3: "6 + 2 * (Suc (length t) div 2) \<le> 2 * length t"
          using \<open>length t \<ge> 6\<close> by presburger
        have 4: "(2::nat) ^ (6 + 2 * (Suc (length t) div 2)) -
                 (take (6 + Suc (length t) div 2 * 2) (rev (flatten t)))\<^sub>2 \<le>
                 2 ^ (2 * length t)" using 3
          by (meson le_diff_conv log2.valid_base power_increasing_iff trans_le_add1)
        have 5: "2 ^ (2 * length t) = (False \<up> (2 * length t) @ [True])\<^sub>2"
          by (rule sym) fact
        show "2 ^ (6 + 2 * (Suc (length t) div 2)) +
              (rev (flatten t) @ [False, True, True])\<^sub>2 -
              (take (6 + Suc (length t) div 2 * 2) (rev (flatten t)))\<^sub>2
              \<le> 2 ^ (2 * length t + 3) - Suc 0" using 1 2 4 5 11 by linarith
      qed
      show "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2
            \<le> (True \<up> (2 * length t + 3))\<^sub>2" using 17 20 by linarith
    qed
    have 4: "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2 \<ge>
             ((replicate (2 * length t) False) @ [False, True, True])\<^sub>2"
    proof -
      have 3: "butlast (rev (flatten t) @ [False, True, True]) =
               rev (flatten t) @ [False, True]" by (simp add: butlast_append)
      have 4: "bij_bin_bin' (rev (flatten t) @ [False, True]) =
               bin'_of_bin (rev (flatten t) @ [False, True])"
        by (smt (verit, best) Nil_is_rev_conv append.assoc append1_eq_conv
            append_Cons bij_bin_bin'.elims rev.simps(2) rev_singleton_conv)
      have 6: "group_2 False (True # False # flatten t) =
               [True, False]#t" using t_wf by (simp add: even_group_2_Cons2)
      note 7 = gn'_inv_def [of "(rev (flatten t) @ [False, True, True])\<^sub>2",
          unfolded gn_inv_def, simplified, unfolded 3 4, simplified, unfolded 5]
      have 8: "(4::nat) ^ (3 + length ([True, False] # t) div 2) =
               2 ^ (6 + length ([True, False] # t) div 2 * 2)" apply simp
        by (metis (no_types, lifting) mult_2_right numeral_Bit0 power_add
            power_mult_distrib)
      have 9: "length (rev (flatten t) @ [False, True, True]) >
               6 + length ([True, False] # t) div 2 * 2" using 1 by simp
      have 10: "(rev (flatten t) @ [False, True, True])\<^sub>2 \<ge>
                4 ^ (3 + length ([True, False] # t) div 2)" unfolding 8
        using length_bin_of_nat_le_iff [of "(rev (flatten t) @ [False, True, True])\<^sub>2"
            "6 + length ([True, False] # t) div 2 * 2"] 9 by simp
      have 11: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 =
                (replicate (2 * length t) False @ [True])\<^sub>2"
        unfolding bin_app_sub_same_prefix by simp
      also have "... = 2 ^ (2 * length t)" by (simp add: nat_of_bin_append1)
      finally have 12: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                        (rev (flatten t) @ [False, True, True])\<^sub>2 =
                        2 ^ (2 * length t)" .
      have 13: "6 + 2 * (Suc (length t) div 2) - 2 * length t = 0" using 1 apply simp
        using nat_le_linear nle_le by fastforce
      have 14: "length (False \<up> (6 + 2 * (Suc (length t) div 2)) @
                drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t))) \<ge>
                2 * length t"
        using 1 by simp
      have 15: "(rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2) \<ge>
                ((replicate (2 * length t) False) @ [False, True, True])\<^sub>2"
        unfolding nmn_mod_pow4m_nat_of_bin apply simp
        unfolding 13 apply simp
        apply (subst append_assoc [symmetric])
        apply (rule nat_of_bin_app_le)
         apply auto
        using 13 diff_is_0_eq le_add_diff_inverse by blast
      show "((replicate (2 * length t) False) @ [False, True, True])\<^sub>2
            \<le> adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2" using 15
        unfolding adj_square'_def
        using 6 7 le_trans next_sq_correct2 suffix'_len_def by presburger
    qed
    have 5: "suffix [True, True] ((replicate (2 * length t) False) @
             [False, True, True])" by simp
    have 6: "suffix [True, True] (replicate (2 * length t + 3) True)"
      by (simp add: bin'_repl)
    have 7: "suffix [True, True] (bin_of_nat (adj_square' (rev (flatten t) @
             [False, True, True])\<^sub>2))"
      apply (rule suffix_bin_of_nat_between)
             apply (fact 5)
            apply (fact 6)
           apply simp_all
         apply (metis append.assoc eval_nat_numeral(3) replicate_Suc replicate_add
          replicate_append_same)
      using adj_square'_def next_sq_gt0 apply presburger
      using 3 4 by simp_all
    show ?case apply simp using 7
      by (metis butlast.simps(2) butlast_append list.distinct(1) suffix_def)
    next
      case (6 t)
      then show ?case by simp
    next
      case (7 t)
      then show ?case by simp
    next
      case (8 b1 b2 b3 t' t)
      then show ?case by blast
    qed
    have 4: "butlast (butlast (bin_of_nat (adj_square'
             (Goedel_Numbering.gn' w))))@[True] =
             butlast (bin_of_nat (adj_square' (Goedel_Numbering.gn' w)))"
      using 3 by auto
    note 5 = l [unfolded w' adj_sq\<^sub>w'_def gn'_inv_def gn_inv_def]
    note 6 = eT_length_bij_bin_bin' [OF 3]
    have 7: "Suc (length (butlast (bin_of_nat (adj_square'
             (Goedel_Numbering.gn' w))))) div 2 = length w" using 5 6 by simp
    have 8: "length (bin_of_nat (adj_square'
             (Goedel_Numbering.gn' w))) div 2 = length w" using 7 by simp
    have 9: "length (bin_of_nat (adj_square' (Goedel_Numbering.gn' w))) =
             length (bin_of_nat (Goedel_Numbering.gn' w))"
      using assms(1, 3) w_wf
    proof (induction w rule: bij_bin'_bin.induct)
      case 1
      then show ?case by simp
    next
      case (2 t)
      then show ?case by simp
    next
      case (3 t)
      then show ?case by simp
    next
      case (4 b t)
      then show ?case by simp
    next
      case (5 t)
      have t_wf: "bin'_wf t" using 5(3) by fastforce
    hence [simp]: "length (flatten t) = 2 * length t" by simp
    have 1: "6 \<le> length t" using 5 by simp
    have 2: "12 \<le> length (flatten t)" using 5(3) [THEN bin'_wf_ConsD] 1 by simp
    have 3: "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2 \<le>
             (replicate (2 * length t + 3) True)\<^sub>2"
    proof -
      have 3: "butlast (rev (flatten t) @ [False, True, True]) =
               rev (flatten t) @ [False, True]" by (simp add: butlast_append)
      have 4: "bij_bin_bin' (rev (flatten t) @ [False, True]) =
               bin'_of_bin (rev (flatten t) @ [False, True])"
        by (smt (verit, best) Nil_is_rev_conv append.assoc append1_eq_conv
            append_Cons bij_bin_bin'.elims rev.simps(2) rev_singleton_conv)
      have 6: "group_2 False (True # False # flatten t) =
               [True, False]#t" using t_wf by (simp add: even_group_2_Cons2)
      note 7 = gn'_inv_def [of "(rev (flatten t) @ [False, True, True])\<^sub>2",
          unfolded gn_inv_def, simplified, unfolded 3 4, simplified, unfolded 5]
      have 8: "(4::nat) ^ (3 + length ([True, False] # t) div 2) =
               2 ^ (6 + length ([True, False] # t) div 2 * 2)" apply simp
        by (metis (no_types, lifting) mult_2_right numeral_Bit0 power_add
            power_mult_distrib)
      have 9: "length (rev (flatten t) @ [False, True, True]) >
               6 + length ([True, False] # t) div 2 * 2" using 1 by simp
      have 10: "(rev (flatten t) @ [False, True, True])\<^sub>2 \<ge>
                4 ^ (3 + length ([True, False] # t) div 2)" unfolding 8
        using length_bin_of_nat_le_iff [of "(rev (flatten t) @ [False, True, True])\<^sub>2"
            "6 + length ([True, False] # t) div 2 * 2"] 9 by simp
      have 11: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 =
                (replicate (2 * length t) False @ [True])\<^sub>2"
        unfolding bin_app_sub_same_prefix by simp
      also have "... = 2 ^ (2 * length t)" by (simp add: nat_of_bin_append1)
      finally have 12: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                        (rev (flatten t) @ [False, True, True])\<^sub>2 =
                        2 ^ (2 * length t)" .
      have 13: "6 + 2 * (Suc (length t) div 2) - 2 * length t = 0" using 1 apply simp
        using nat_le_linear nle_le by fastforce
      have 14: "length (False \<up> (6 + 2 * (Suc (length t) div 2)) @
                drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t))) \<ge>
                2 * length t"
        using 1 by simp
      have 15: "(rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2) \<ge>
                ((replicate (2 * length t) False) @ [False, True, True])\<^sub>2"
        unfolding nmn_mod_pow4m_nat_of_bin apply simp
        unfolding 13 apply simp
        apply (subst append_assoc [symmetric])
        apply (rule nat_of_bin_app_le)
         apply auto
        using 13 diff_is_0_eq le_add_diff_inverse by blast
      note 16 = nmn_mod_pow4m_nat_of_bin
        [of "(rev (flatten t) @ [False, True, True])\<^sub>2"
          "(3 + length ([True, False] # t) div 2)", simplified,
          unfolded nat_of_bin_app_0s]
      have 17: "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2 -
                ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2)) <
                2 ^ (6 + 2 * (Suc (length t) div 2))" unfolding adj_square'_def
      proof (simp del: next_sq_def)
        have 17: "(rev (flatten t) @ [False, True, True])\<^sub>2 -
              (rev (flatten t) @ [False, True, True])\<^sub>2 mod
              4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2) =
              (drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t)) @
              drop (6 + 2 * (Suc (length t) div 2) - 2 * length t)
              [False, True, True])\<^sub>2 * 2 ^ (6 + 2 * (Suc (length t) div 2))"
          unfolding 16 [symmetric] by (simp add: 7 suffix'_len_def)
        have 18: "(drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t)) @
                  [False, True, True])\<^sub>2 * 2 ^ (6 + 2 * (Suc (length t) div 2)) +
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  2 ^ (6 + Suc (length t) div 2 * 2) =
                  (rev (flatten t) @ [False, True, True])\<^sub>2"
          by (metis 13 16 8 add.commute drop0 le_add_diff_inverse length_Cons
              mod_less_eq_dividend)
        have 19: "next_square ((drop (6 + 2 * (Suc (length t) div 2))
                  (rev (flatten t)) @ [False, True, True])\<^sub>2 *
                  2 ^ (6 + 2 * (Suc (length t) div 2))) +
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  2 ^ (6 + Suc (length t) div 2 * 2)
                  \<ge> (rev (flatten t) @ [False, True, True])\<^sub>2"
          using 18 by (metis diff_add_inverse2 le_diff_conv next_sq_correct2)
        have 20: "4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2) =
                  4 ^ (3 + Suc (length t) div 2)"
          by (simp add: 7 suffix'_len_def)
        have 21: "next_square ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod 4 ^ (3 + Suc (length t)
                  div 2)) - ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod 4 ^ (3 + Suc (length t)
                  div 2)) =
                  next_square ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  4 ^ suffix'_len (gn'_inv (rev (flatten t) @
                  [False, True, True])\<^sub>2)) + (rev (flatten t) @ [False, True, True])\<^sub>2
                  mod 4 ^ (3 + Suc (length t) div 2) -
                  (rev (flatten t) @ [False, True, True])\<^sub>2" by (simp add: 20)
        have 22: "4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2)))
                  div 2 \<le> 6 + 2 * (Suc (length t) div 2)" by simp
        have 23: "4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  4 ^ (3 + Suc (length t) div 2))) - 1) div 2 \<le>
                  4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2)))
                  div 2" using bit_length_sub
          by (meson diff_le_self div_le_mono nat_add_left_cancel_le
              order_trans_rules(23))
        have 24: "4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                  (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                  4 ^ (3 + Suc (length t) div 2))) - 1) div 2 \<le>
                  6 + 2 * (Suc (length t) div 2)" using 22 23 by linarith
        show "next_square
              ((rev (flatten t) @ [False, True, True])\<^sub>2 -
              (rev (flatten t) @ [False, True, True])\<^sub>2 mod
              4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2)) +
              (rev (flatten t) @ [False, True, True])\<^sub>2 mod
              4 ^ (3 + Suc (length t) div 2) - (rev (flatten t) @
              [False, True, True])\<^sub>2 < 2 ^ (6 + 2 * (Suc (length t) div 2))"
          using next_sq_diff [of "(rev (flatten t) @ [False, True, True])\<^sub>2 -
      (rev (flatten t) @ [False, True, True])\<^sub>2 mod
      4 ^ suffix'_len (gn'_inv (rev (flatten t) @ [False, True, True])\<^sub>2)"]
          unfolding 20 21 using 24 by (meson length_bin_of_nat_le_iff
              order_trans_rules(23))
      qed
      have 18: "(replicate (2 * length t + 3) True)\<^sub>2 = 2 ^ (2 * length t + 3) - Suc 0"
        by simp
      have 19: "take (6 + Suc (length t) div 2 * 2 - 2 * length t)
                [False, True, True] = []" using 1 13 by auto
      have 20: "((2::nat) ^ (6 + 2 * (Suc (length t) div 2))) +
                ((rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2)) \<le>
                (True \<up> (2 * length t + 3))\<^sub>2" apply simp
        unfolding 8 [simplified] take_mod apply simp
        unfolding 19
      proof simp
        have 1: "(rev (flatten t) @ [False, True, True])\<^sub>2 \<le>
                 2 ^ (2 * length t + 3) - Suc 0" using 1 t_wf
          by (smt (z3) Suc_pred \<open>length (flatten t) = 2 * length t\<close> length_Cons
              length_append length_rev less_Suc_eq_le list.size(3) nat_of_bin_max
              numeral_3_eq_3 pos2 zero_less_power)
        have 2: "(rev (flatten t) @ [True, True, True])\<^sub>2 \<le>
                 2 ^ (2 * length t + 3) - Suc 0"
          by (smt (z3) Suc_pred \<open>length (flatten t) = 2 * length t\<close> length_Cons
              length_append length_rev less_Suc_eq_le list.size(3) nat_of_bin_max
              numeral_3_eq_3 pos2 zero_less_power)
        have 3: "6 + 2 * (Suc (length t) div 2) \<le> 2 * length t"
          using \<open>length t \<ge> 6\<close> by presburger
        have 4: "(2::nat) ^ (6 + 2 * (Suc (length t) div 2)) -
                 (take (6 + Suc (length t) div 2 * 2) (rev (flatten t)))\<^sub>2 \<le>
                 2 ^ (2 * length t)" using 3
          by (meson le_diff_conv log2.valid_base power_increasing_iff trans_le_add1)
        have 5: "2 ^ (2 * length t) = (False \<up> (2 * length t) @ [True])\<^sub>2"
          by (rule sym) fact
        show "2 ^ (6 + 2 * (Suc (length t) div 2)) +
              (rev (flatten t) @ [False, True, True])\<^sub>2 -
              (take (6 + Suc (length t) div 2 * 2) (rev (flatten t)))\<^sub>2
              \<le> 2 ^ (2 * length t + 3) - Suc 0" using 1 2 4 5 11 by linarith
      qed
      show "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2
            \<le> (True \<up> (2 * length t + 3))\<^sub>2" using 17 20 by linarith
    qed
    have 4: "adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2 \<ge>
             ((replicate (2 * length t) False) @ [False, True, True])\<^sub>2"
    proof -
      have 3: "butlast (rev (flatten t) @ [False, True, True]) =
               rev (flatten t) @ [False, True]" by (simp add: butlast_append)
      have 4: "bij_bin_bin' (rev (flatten t) @ [False, True]) =
               bin'_of_bin (rev (flatten t) @ [False, True])"
        by (smt (verit, best) Nil_is_rev_conv append.assoc append1_eq_conv
            append_Cons bij_bin_bin'.elims rev.simps(2) rev_singleton_conv)
      have 6: "group_2 False (True # False # flatten t) =
               [True, False]#t" using t_wf by (simp add: even_group_2_Cons2)
      note 7 = gn'_inv_def [of "(rev (flatten t) @ [False, True, True])\<^sub>2",
          unfolded gn_inv_def, simplified, unfolded 3 4, simplified, unfolded 5]
      have 8: "(4::nat) ^ (3 + length ([True, False] # t) div 2) =
               2 ^ (6 + length ([True, False] # t) div 2 * 2)" apply simp
        by (metis (no_types, lifting) mult_2_right numeral_Bit0 power_add
            power_mult_distrib)
      have 9: "length (rev (flatten t) @ [False, True, True]) >
               6 + length ([True, False] # t) div 2 * 2" using 1 by simp
      have 10: "(rev (flatten t) @ [False, True, True])\<^sub>2 \<ge>
                4 ^ (3 + length ([True, False] # t) div 2)" unfolding 8
        using length_bin_of_nat_le_iff [of "(rev (flatten t) @ [False, True, True])\<^sub>2"
            "6 + length ([True, False] # t) div 2 * 2"] 9 by simp
      have 11: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 =
                (replicate (2 * length t) False @ [True])\<^sub>2"
        unfolding bin_app_sub_same_prefix by simp
      also have "... = 2 ^ (2 * length t)" by (simp add: nat_of_bin_append1)
      finally have 12: "(rev (flatten t) @ [True, True, True])\<^sub>2 -
                        (rev (flatten t) @ [False, True, True])\<^sub>2 =
                        2 ^ (2 * length t)" .
      have 13: "6 + 2 * (Suc (length t) div 2) - 2 * length t = 0" using 1 apply simp
        using nat_le_linear nle_le by fastforce
      have 14: "length (False \<up> (6 + 2 * (Suc (length t) div 2)) @
                drop (6 + 2 * (Suc (length t) div 2)) (rev (flatten t))) \<ge>
                2 * length t"
        using 1 by simp
      have 15: "(rev (flatten t) @ [False, True, True])\<^sub>2 -
                (rev (flatten t) @ [False, True, True])\<^sub>2 mod
                4 ^ (3 + length ([True, False] # t) div 2) \<ge>
                ((replicate (2 * length t) False) @ [False, True, True])\<^sub>2"
        unfolding nmn_mod_pow4m_nat_of_bin apply simp
        unfolding 13 apply simp
        apply (subst append_assoc [symmetric])
        apply (rule nat_of_bin_app_le)
         apply auto
        using 13 diff_is_0_eq le_add_diff_inverse by blast
      show "((replicate (2 * length t) False) @ [False, True, True])\<^sub>2
            \<le> adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2" using 15
        unfolding adj_square'_def
        using 6 7 le_trans next_sq_correct2 suffix'_len_def by presburger
    qed
    have 6: "suffix [True, True] ((replicate (2 * length t) False) @ [False, True, True])" by simp
    have 7: "suffix [True, True] (True \<up> (2 * length t + 3))"
      by (metis bin'_repl eval_nat_numeral(3) replicate_Suc replicate_add
          suffix_ConsI suffix_appendI suffix_order.dual_order.refl)
    have 71: "ends_in True (True \<up> (2 * length t + 3))" using 7
      by (metis append_assoc eval_nat_numeral(3) replicate_Suc replicate_add
          replicate_append_same)
    have 8: "\<exists>ys. bin_of_nat (adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2) =
             ys @ [True]"
      using adj_square'_def bin_of_nat_gt_0_end_True next_sq_gt0 by presburger
    have 9: "(bin_of_nat (adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2))\<^sub>2
             \<le> 2 ^ (2 * length t + 3) - Suc 0"
      by (metis 3 One_nat_def nat_bin_nat nat_of_bin_all_True)
    have 10: "(False \<up> (2 * length t) @ [False, True, True])\<^sub>2
              \<le> (bin_of_nat (adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2))\<^sub>2"
      by (simp add: 4)
    note 11 = suffix_bin_of_nat_between [OF 6 7, simplified, OF 71 8 9 10]
    hence 12: "\<exists>x. bin_of_nat (adj_square' (rev (flatten t) @ [False, True, True])\<^sub>2) =
               x @ [True, True]" by (metis append_take_drop_id)
    have 13: "length (rev (flatten t) @ [True, True, True]) =
              length (rev (flatten t) @ [False, True, True])" by simp
    have 14: "ends_in True (replicate (2 * length t + 3) True)" by fact
    have 15: "length (bin_of_nat (adj_square' (rev (flatten t) @
              [False, True, True])\<^sub>2)) =
              length ((replicate (2 * length t) False) @ [False, True, True])"
      apply (rule length_bin_of_nat_between)
           apply simp_all
          apply (fact 14)
      using 8 apply blast
        apply simp
      by fact+
    show ?case using 5 apply auto
      apply (drule bin'_wf_ConsD)
      unfolding gn'_defs gn_defs apply simp
      unfolding 15 by simp
    next
      case (6 t)
      then show ?case by simp
    next
      case (7 t)
      then show ?case by simp
    next
      case (8 b1 b2 b3 t' t)
      then show ?case by blast
    qed
    have 10: "odd (length (rev (bin_of_nat (adj_square' (Goedel_Numbering.gn' w)))))"
      apply simp unfolding 9
      apply (rule starts_with_TF_odd_length_gn')
      by fact+
    show "take (length w - k) w =
          take (length w - k) (gn'_inv (adj_square' (Goedel_Numbering.gn' w)))"
      unfolding gn'_inv_def gn_inv_def apply (subst 4 [symmetric])
      unfolding bij_bin_bin'.simps apply simp
      unfolding 1 [symmetric] rev_butlast_is_tl_rev apply simp
      unfolding odd_length_tl_group_2 [OF 10]
      by (metis 4 butlast_rev rev.simps(2) rev_rev_ident)
  qed
  then show "take (length w - k) w' = take (length w - k) w" ..
qed

lemma sh_pfx_log_ineq':
  assumes "l \<ge> 18"
  defines "l_div_2 \<equiv> l div 2"
  shows "nat_log_ceil 2 l \<le> l div 2 - 4"
proof -
  have "l div 2 \<ge> 5" using \<open>l \<ge> 18\<close> by linarith

  have "nat_log_ceil 2 l \<le> nat_log 2 l + 1" by (fact log2.ceil_le_nat_log_p1)
  also have "... \<le> l div 2 - 5 + 1" unfolding add_le_cancel_right
    using \<open>l \<ge> 18\<close> by (rule sh_pfx_log_ineq)
  also have "... = l div 2 + 1 - 5" using \<open>l div 2 \<ge> 5\<close> by (rule add_diff_assoc2)
  also have "... = l div 2 - (5 - 1)" using \<open>l div 2 \<ge> 5\<close> by (intro diff_diff_right[symmetric]) simp
  also have "... = l div 2 - 4" by force
  finally show ?thesis .
qed

theorem adj'_sq'_sh_pfx_log:
  fixes w
  defines "l \<equiv> length w"
  defines "w' \<equiv> adj_sq\<^sub>w' w"
  assumes "l \<ge> 18" \<comment> \<open>lower bound for \<open>clog l \<le> l div 2 - 4\<close>\<close> and
          "set w \<subseteq> {w. length w = 2}" and
          "starts_with [True, False] w"
  shows "shared_MSBs' (nat_log_ceil 2 l) w w'"
proof -
  have "nat_log_ceil 2 l \<le> l div 2 - 3" using sh_pfx_log_ineq' [OF \<open>l \<ge> 18\<close>] by simp
  also have "... = l div 2 + l div 2 - l div 2 - 3" unfolding diff_add_inverse2 ..
  also have "... \<le> l - l div 2 - 3" using assms(3) by fastforce
  also have "... = l - (3 + l div 2)" unfolding diff_diff_left by presburger
  also have "... \<le> length w - suffix'_len w" unfolding suffix'_len_def assms(1) ..
  finally have "nat_log_ceil 2 l \<le> length w - suffix'_len w" .

  moreover have "shared_MSBs' (length w - suffix'_len w) w (adj_sq\<^sub>w' w)" using \<open>l \<ge> 18\<close>
    apply (intro adj_sq'_sh_pfx_half)
    unfolding l_def using assms by auto
  ultimately show "shared_MSBs' (nat_log_ceil 2 l) w w'"
    by (fold w'_def) (rule sh'_msb_le)
qed

lemma problem1: "4 ^ (3 + length (replicate n [False, False]@[[True, False]]@replicate 7 [False, False]) div 2) <
                 (bij_bin'_bin (replicate n [False, False]@[[True, False]]@replicate 7 [False, False]) @ [True])\<^sub>2"
proof simp
  have 1: "bij_bin'_bin ([False, False] \<up> n @ [True, False] # [False, False] \<up> 7) =
           (replicate 14 False) @ [False, True] @ replicate n False"
  proof (induction n)
    case 0
    then show ?case apply simp
      by (metis bin'_repl flatten_repl_repl numeral_Bit0_eq_double rev_replicate)
  next
    case (Suc n)
    then show ?case by (simp add: replicate_append_same)
  qed
  have 2: "(4::nat) ^ (3 + (n + 8) div 2) = 2 ^ (6 + (n + 8) div 2 * 2)"
    by (metis distrib_left mult.commute numeral_Bit0_eq_double power2_eq_square power_mult)
  have 3: "(False \<up> 14 @ False # True # False \<up> n @ [True])\<^sub>2 = 2 ^ (16 + n) + 2 ^ 15"
  proof (induction n)
    case 0
    have 1: "(replicate k False @ w)\<^sub>2 = (w)\<^sub>2 * 2 ^ k" for k :: nat and w :: bin
    proof (induction k)
      case 0
      then show ?case by simp
    next
      case (Suc k)
      then show ?case by simp
    qed
    show ?case apply simp unfolding 1 by simp
  next
    case (Suc n)
    have 1: "(replicate k False @ w)\<^sub>2 = (w)\<^sub>2 * 2 ^ k" for k :: nat and w :: bin
    proof (induction k)
      case 0
      then show ?case by simp
    next
      case (Suc k)
      then show ?case by simp
    qed
    show ?case apply simp unfolding 1 apply simp unfolding 1 apply simp
    proof (induction n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      then show ?case apply simp
        by (metis (mono_tags, lifting) One_nat_def mult.assoc numeral_1_eq_Suc_0
            numeral_Bit0_eq_double power_add power_add_numeral2 power_one_right
            semiring_norm(4) semiring_norm(5))
    qed
  qed
  show "4 ^ (3 + (n + 8) div 2)
        < (bij_bin'_bin ([False, False] \<up> n @ [True, False] # [False, False] \<up> 7) @ [True])\<^sub>2"
    unfolding 1 2 apply simp unfolding 3 apply simp
  proof -
    have "(2::nat) ^ (6 + (n + 8) div 2 * 2) < 2 ^ (16 + n div 2 * 2)" by simp
    also have "... \<le> 2 ^ (16 + n)" by simp
    also have "... \<le> 2 ^ (16 + n) + 32768" by simp
    finally show "(2::nat) ^ (6 + (n + 8) div 2 * 2) < 2 ^ (16 + n) + 32768" .
  qed
qed

(* This lemma shows that the current Gödelisation is not ideal for proving L\<^sub>0 \<notin> DTIME t
   (see L0.thy), as the proof requires \<And>w. length (adj_sq\<^sub>w' w) \<le> length w. This lemma
   gives a counterexample to this. *)
lemma problem2: "length (adj_sq\<^sub>w' (replicate 10 [False, False]@[[True, False]]@replicate 7 [False, False])) >
                 length (replicate 10 [False, False]@[[True, False]]@replicate 7 [False, False])"
  apply simp
  unfolding gn'_defs gn_defs adj_square'_def apply (simp del: next_sq_def)
  apply (subst bij_bin_bin'_bin)
   apply fastforce
proof -
  have 1: "bij_bin'_bin ([False, False] \<up> n @ [True, False] # [False, False] \<up> 7) =
           (replicate 15 False @ [True] @ replicate n False)" for n :: nat
    apply (induction n)
     apply auto
     apply (simp add: numeral_eq_Suc)
    by (simp add: replicate_append_same)
  have 2: "(False \<up> n @ True # False \<up> k @ [True])\<^sub>2 = 2 ^ n + 2 ^ (n + k + 1)" for n k :: nat
    apply (induction n)
     apply auto
    by (simp add: nat_of_bin_append1)
  have 3: "dsqrt 67108863 = 8191"
    unfolding Discrete_Functions.floor_sqrt_def
  proof -
    have "(8191::nat)\<^sup>2 \<le> 67108863" by simp
    hence "Max {m. m\<^sup>2 \<le> 67108863} \<ge> (8191::nat)"
      using Discrete_Functions.floor_sqrt_def le_floor_sqrt_iff by presburger
    moreover have "(8192::nat)\<^sup>2 > 67108863" by simp
    hence "Max {m. m\<^sup>2 \<le> 67108863} < (8192::nat)"
      by (metis Discrete_Functions.floor_sqrt_def le_floor_sqrt_iff linorder_not_less)
    ultimately show "Max {m. m\<^sup>2 \<le> 67108863} = (8191::nat)" by simp
  qed
  have 4: "(67108864::nat) = 2 ^ 26" by simp
  have 5: "bin_of_nat (2 ^ 26) = (replicate 26 False)@[True]"
    by (metis 4 One_nat_def add_Suc_shift bin_nat_bin length_replicate
        nat_of_bin_0s nat_of_bin_app1 numeral_eq_Suc plus_1_eq_Suc)
  show "18 < length (bij_bin_bin' (butlast (bin_of_nat (next_square
        ((bij_bin'_bin ([False, False] \<up> 10 @ [True, False] # [False, False] \<up> 7) @
        [True])\<^sub>2 - (bij_bin'_bin ([False, False] \<up> 10 @ [True, False] # [False, False] \<up> 7) @
        [True])\<^sub>2 mod 4 ^ suffix'_len ([False, False] \<up> 10 @ [True, False] #
        [False, False] \<up> 7))))))" unfolding 1 apply (simp del: next_sq_def)
    unfolding suffix'_len_def apply (simp del: next_sq_def)
    unfolding 2 apply (simp del: next_sq_def) (* 67108864 is already a square *)
    apply simp
    unfolding 3 apply simp (* 67108864 is 2 ^ 26 *)
    unfolding 4 5 apply simp (* "butlast" eliminates the leading 1, hence "False \<up> 26"
                                 remains *)
    unfolding bij_bin_bin'_repl_F
    unfolding length_replicate
    by simp
qed

lemma next_sq_le_square: "n \<ge> 2 \<Longrightarrow> next_square n \<le> n\<^sup>2"
proof (induction n rule: nat_induct_at_least)
  case base
  then show ?case apply simp
    by (metis One_nat_def numeral_2_eq_2 numeral_Bit0_eq_double order_le_less
        power2_eq_square floor_sqrt_one)
next
  case (Suc n)
  then show ?case by (simp add: floor_sqrt_le)
qed

lemma adj_square'_le_square: "n > 0 \<Longrightarrow> adj_square' n \<le> n\<^sup>2"
  unfolding adj_square'_def suffix'_len_def gn'_inv_def gn_inv_def
proof (cases "n < 4 ^ (3 + length (bij_bin_bin' (butlast (bin_of_nat n))) div 2)")
  assume a1: "n > 0"
  case True
  hence "n mod 4 ^ (3 + length (bij_bin_bin' (butlast
         (bin_of_nat n))) div 2) = n" by (rule mod_less)
  hence "n - n mod 4 ^ (3 + length (bij_bin_bin' (butlast (bin_of_nat n))) div 2) = 0"
    by simp
  then show "next_square (n - n mod 4 ^ (3 + length (bij_bin_bin' (butlast
             (bin_of_nat n))) div 2)) \<le> n\<^sup>2" using a1 by simp
next
  case False
  hence 1: "n \<ge> 2"
    by (metis One_nat_def add_is_0 le_neq_implies_less less_2_cases_iff nat_one_le_power
        nat_power_eq_Suc_0_iff nat_zero_less_power_iff not_le_imp_less numeral_1_eq_Suc_0
        numeral_eq_iff one_le_numeral verit_eq_simplify(10) zero_less_numeral
        zero_neq_numeral)
  show "next_square (n - n mod 4 ^ (3 + length (bij_bin_bin' (butlast
             (bin_of_nat n))) div 2)) \<le> n\<^sup>2" using next_sq_le_square [OF 1]
    by (meson diff_le_self next_square_mono order_trans_rules(23))
qed

(* Used in lemma L\<^sub>0 \<notin> DTIME t (file L0.thy) *)
lemma length_adj_sq_le: "bin'_wf w \<Longrightarrow> length (adj_sq\<^sub>w' w) \<le> 2 * length w"
  apply (auto simp add: gn'_defs gn_defs)
proof (induction w rule: bij_bin'_bin.induct)
  case 1
  then show ?case by (simp add: adj_square'_def)
next
  have 1: "\<And>t. butlast (bij_bin'_bin t @ [False, True]) =
           bij_bin'_bin t @ [False]" by (simp add: butlast_append)
  case (2 t)
  then show ?case apply (auto dest!: bin'_wf_ConsD simp add: adj_square'_def
        simp del: next_sq_def)
    unfolding gn'_defs gn_defs apply (simp del: next_sq_def add: 1 suffix'_len_def)
    apply (cases "(bij_bin'_bin t @ [False, True])\<^sub>2 < 4 ^ (3 + Suc (length t) div 2)")
     apply simp
  proof -
    have t_wf: "bin'_wf t" using 2(2) by fastforce
    assume a1: "length (bij_bin_bin' (butlast (bin_of_nat (next_square
                ((bij_bin'_bin t @ [True])\<^sub>2 - (bij_bin'_bin t @ [True])\<^sub>2 mod
                4 ^ (3 + length t div 2)))))) \<le> 2 * length t" and a2: "bin'_wf t" and
           a3: "\<not> (bij_bin'_bin t @ [False, True])\<^sub>2 < 4 ^ (3 + Suc (length t) div 2)"
    have 3: "(bij_bin'_bin t @ [False, True])\<^sub>2 \<ge> 4 ^ (3 + Suc (length t) div 2)"
      using a3 by simp
    have 4: "bit_length ((bij_bin'_bin t @ [False, True])\<^sub>2 -
             (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2)) \<le>
             length (bij_bin'_bin t @ [False, True])"
      apply simp
      by (smt (z3) One_nat_def Suc_1 add_2_eq_Suc' bit_length_sub le_trans len_bin_nat_bin
          length_Cons length_append list.size(3))
    have 5: "(4::nat) ^ (3 + Suc (length t) div 2) =
               2^(6 + (Suc (length t) div 2) * 2)"
        by (metis (no_types, lifting) mult_2_right numeral_Bit0 power_add power_mult_distrib)
    have 6: "bit_length ((bij_bin'_bin t @ [False, True])\<^sub>2 -
             (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2)) \<ge>
             length (bij_bin'_bin t @ [False, True])"
    proof -
      have 6: "(bij_bin'_bin t @ [False, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) \<ge> 1"
        using 3
        by (metis One_nat_def Suc_leI div_greater_zero_iff nat_zero_less_power_iff
            zero_less_numeral)
      show "bit_length ((bij_bin'_bin t @ [False, True])\<^sub>2 -
            (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2)) \<ge>
            length (bij_bin'_bin t @ [False, True])"
        unfolding minus_mod_eq_div_mult 5
        apply (subst bit_length_mult_pow2)
         apply auto
         apply (metis 5 6 not_gr0 not_one_le_zero)
        unfolding bit_length_div_pow2 by simp
    qed
    have 7: "bit_length ((bij_bin'_bin t @ [False, True])\<^sub>2 -
             (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2)) =
             length (bij_bin'_bin t @ [False, True])" using 4 6 by linarith
    have 8: "prefix (replicate (6 + Suc (length t) div 2 * 2) False)
             (bin_of_nat ((bij_bin'_bin t @ [False, True])\<^sub>2 -
             (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2)))"
      unfolding prefix_take_iff minus_mod_eq_div_mult 5 apply simp
      apply (subst take_mult_pow2)
       apply (metis 5 Euclidean_Rings.div_eq_0_iff a3 gr0I pos2 power_not_zero)
      ..
    have 9: "bit_length (next_square ((bij_bin'_bin t @ [False, True])\<^sub>2 -
             (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2))) =
             bit_length ((bij_bin'_bin t @ [False, True])\<^sub>2 -
             (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2))"
    proof -
      obtain k :: nat where k_def: "(bij_bin'_bin t @ [False, True])\<^sub>2 -
            (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2) + k =
            next_square ((bij_bin'_bin t @ [False, True])\<^sub>2 -
            (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2))"
        using le_add_diff_inverse next_sq_correct2 by blast
      have 9: "k < 2^(4 + (length (bij_bin'_bin t @ [False, True]) - 1) div 2)"
        using k_def next_sq_diff [of "(bij_bin'_bin t @ [False, True])\<^sub>2 -
            (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2)"]
        unfolding 7 by (metis diff_add_inverse)
      have 10: "bit_length k \<le> 4 + (length (bij_bin'_bin t @ [False, True]) - 1) div 2"
        using 9 bit_len_le_pow2 by blast
      have 11: "4 + (length (bij_bin'_bin t @ [False, True]) - 1) div 2 \<le>
                6 + Suc (length t) div 2 * 2"
        using length_bij_bin'_bin_upper_bound [OF t_wf] by simp
      have 12: "take (6 + Suc (length t) div 2 * 2)
                (bin_of_nat ((bij_bin'_bin t @ [False, True])\<^sub>2 -
                (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2))) =
                replicate (6 + Suc (length t) div 2 * 2) False"
        unfolding 5 by (metis (no_types, lifting) 5 8 length_replicate prefix_take_iff)
      show "bit_length (next_square ((bij_bin'_bin t @ [False, True])\<^sub>2 -
            (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2))) =
            bit_length ((bij_bin'_bin t @ [False, True])\<^sub>2 -
            (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2))"
        using 10 11 12 by (smt (verit, del_insts) 3 5 div_greater_zero_iff k_def le_trans
            length_bin_of_nat_le_iff minus_mod_eq_div_mult pos2 suffix_len_eq
            zero_less_power)
    qed
    have 10: "bit_length ((bij_bin'_bin t @ [False, True])\<^sub>2 div
              4 ^ (3 + Suc (length t) div 2) * 4 ^ (3 + Suc (length t) div 2)) =
              length (bij_bin'_bin t @ [False, True])"
      apply simp
      by (metis (no_types, lifting) 7 One_nat_def add.commute add_Suc_shift bin'_repl
          bin'_wf_empty bin'_wf_length bin_of_nat.simps(1) bin_of_nat_double
          bin_of_nat_double_p1 bit_len_even_odd flatten.simps(1) length_append
          length_replicate list.size(3) minus_mod_eq_mult_div mult.commute numeral_2_eq_2
          plus_1_eq_Suc zero_less_one)
    have "next_square ((bij_bin'_bin t @ [False, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
          4 ^ (3 + Suc (length t) div 2)) -
          (bij_bin'_bin t @ [False, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
          4 ^ (3 + Suc (length t) div 2) < 2 ^ (4 + Suc (length (bij_bin'_bin t)) div 2) \<Longrightarrow>
          next_square ((bij_bin'_bin t @ [False, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
          4 ^ (3 + Suc (length t) div 2)) -
          (bij_bin'_bin t @ [False, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
          4 ^ (3 + Suc (length t) div 2) < 2 ^ (4 + Suc (length t * 2) div 2)"
      using length_bij_bin'_bin_upper_bound [OF t_wf]
      by (smt (verit, ccfv_SIG) add_mono_thms_linordered_semiring(2) distrib_left
          div_le_mono log2.valid_base mult_2 nat_mult_1_right order_less_le_trans
          plus_1_eq_Suc power_increasing_iff)
    hence 11: "next_square ((bij_bin'_bin t @ [False, True])\<^sub>2 div
               4 ^ (3 + Suc (length t) div 2) * 4 ^ (3 + Suc (length t) div 2)) -
               (bij_bin'_bin t @ [False, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
               4 ^ (3 + Suc (length t) div 2) <
               2 ^ (4 + Suc (length (bij_bin'_bin t)) div 2) \<Longrightarrow>
               next_square ((bij_bin'_bin t @ [False, True])\<^sub>2 div
               4 ^ (3 + Suc (length t) div 2) * 4 ^ (3 + Suc (length t) div 2)) -
               (bij_bin'_bin t @ [False, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
               4 ^ (3 + Suc (length t) div 2) \<le> 2 ^ (4 + length t)"
      by (metis bin'_wf_even bin'_wf_length even_Suc_div_two less_imp_le mult.commute
          nonzero_mult_div_cancel_left t_wf zero_neq_numeral)
    have 12: "next_square ((bij_bin'_bin t @ [False, True])\<^sub>2 div
              4 ^ (3 + Suc (length t) div 2) *
              4 ^ (3 + Suc (length t) div 2)) - (bij_bin'_bin t @ [False, True])\<^sub>2
              div 4 ^ (3 + Suc (length t) div 2) * 4 ^ (3 + Suc (length t) div 2) \<le>
              (2 ^ (length t + 4))"
        using next_sq_diff [of "(bij_bin'_bin t @ [False, True])\<^sub>2 div
              4 ^ (3 + Suc (length t) div 2) * 4 ^ (3 + Suc (length t) div 2)"] unfolding 10
        apply (simp del: next_sq_def)
        apply (drule 11)
        by (metis add.commute)
    have 13: "length (bij_bin_bin' (butlast (bin_of_nat (next_square
              ((bij_bin'_bin t @ [False, True])\<^sub>2 -
              (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2)))))) \<le>
              bit_length (next_square ((bij_bin'_bin t @ [False, True])\<^sub>2 -
              (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2))) - 1"
      using length_bij_bin_bin'_upper_bound by (metis length_butlast)
    have 14: "length (bij_bin_bin' (butlast (bin_of_nat (next_square
              ((bij_bin'_bin t @ [False, True])\<^sub>2 -
              (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2)))))) \<le>
              bit_length ((bij_bin'_bin t @ [False, True])\<^sub>2 -
              (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2)) - 1"
      using 13 unfolding 9 .
    have 15: "length (bij_bin_bin' (butlast (bin_of_nat (next_square
              ((bij_bin'_bin t @ [False, True])\<^sub>2 -
              (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2)))))) \<le>
              length (bij_bin'_bin t @ [False, True]) - 1"
      using 14 unfolding 7 .
    show "length (bij_bin_bin' (butlast (bin_of_nat (next_square
          ((bij_bin'_bin t @ [False, True])\<^sub>2 -
          (bij_bin'_bin t @ [False, True])\<^sub>2 mod 4 ^ (3 + Suc (length t) div 2))))))
          \<le> Suc (Suc (2 * length t))" using 15 length_bij_bin'_bin_upper_bound [OF t_wf]
      by simp
  qed
next
  case (3 t)
  then show ?case by fastforce
next
  case (4 b t)
  then show ?case by fastforce
next
  case (5 t)
  hence t_wf: "bin'_wf t" by fastforce
  then show ?case apply (simp del: next_sq_def add: adj_square'_def)
    unfolding gn'_defs gn_defs suffix'_len_def
  proof (simp del: next_sq_def add: minus_mod_eq_div_mult)
    have "3 + length (bij_bin_bin' (butlast (rev (flatten t) @
          [False, True, True]))) div 2 = 3 + length (bij_bin_bin' (rev (flatten t) @
          [False, True])) div 2" by (simp add: butlast_append)
    also have "... = 3 + length (rev (flatten t) @
               [False, True]) div 4" using eT_length_bij_bin_bin' t_wf by auto
    also have "... = 3 + (Suc (length t)) div 2" using t_wf by simp
    finally have 1: "3 + length (bij_bin_bin' (butlast (rev (flatten t) @
                     [False, True, True]))) div 2 = 3 + Suc (length t) div 2" .
    have 2: "(4::nat) ^ (3 + Suc (length t) div 2) = 2 ^ (6 + (Suc (length t) div 2) * 2)"
      by (metis (no_types, lifting) mult_2_right numeral_Bit0 power_add power_mult_distrib)
    note 3 = next_sq_diff [of "(rev (flatten t) @ [False, True, True])\<^sub>2 div
              4 ^ (3 + Suc (length t) div 2) * 4 ^ (3 + Suc (length t) div 2)"]
    show "length (bij_bin_bin' (butlast (bin_of_nat (next_square
          ((rev (flatten t) @ [False, True, True])\<^sub>2 div 4 ^ (3 +
          length (bij_bin_bin' (butlast (rev (flatten t) @ [False, True, True]))) div 2) *
          4 ^ (3 + length (bij_bin_bin' (butlast (rev (flatten t) @
          [False, True, True]))) div 2)))))) \<le> Suc (Suc (2 * length t))"
      unfolding 1
    proof (cases "(rev (flatten t) @ [False, True, True])\<^sub>2 \<le> 4 ^ (3 + Suc (length t) div 2)")
      case 1: True
      then show "length (bij_bin_bin' (butlast (bin_of_nat (next_square
          ((rev (flatten t) @ [False, True, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
          4 ^ (3 + Suc (length t) div 2)))))) \<le> Suc (Suc (2 * length t))"
      proof (cases "(rev (flatten t) @ [False, True, True])\<^sub>2 =
                    4 ^ (3 + Suc (length t) div 2)")
        case 2: True
        have "is_square (4 ^ (3 + Suc (length t) div 2))"
          apply (rule exI [where x="2 ^ (3 + Suc (length t) div 2)"])
          by (metis numeral_Bit0_eq_double power2_eq_square power_even_eq power_mult)
        hence [simp]: "next_square (4 ^ (3 + Suc (length t) div 2)) =
                       4 ^ (3 + Suc (length t) div 2)" using next_sq_eq by auto
        have 1: "(4::nat) ^ (3 + Suc (length t) div 2) = 2 ^ (6 + Suc (length t) div 2 * 2)"
          by (metis (no_types, lifting) mult_2_right numeral_Bit0 power_add
              power_mult_distrib)
        show ?thesis using 2 apply (simp del: next_sq_def)
          unfolding 1 apply simp
          by (smt (z3) add_2_eq_Suc' add_Suc_right bij_bin_bin'_repl_F bin'_wf_length
              len_bin_nat_bin length_Cons length_append length_bin_of_nat_pow2
              length_replicate length_rev list.size(3) not_less_eq_eq numeral_2_eq_2 t_wf)
      next
        case False
        then show ?thesis using 1 by simp
      qed
    next
      case False
      have 4: "4 + (length (bin_of_nat
               ((rev (flatten t) @ [False, True, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
               4 ^ (3 + Suc (length t) div 2))) - 1) div 2 = 5 + length t" apply simp
        unfolding 2 apply (subst bit_length_div_mult_eq)
        using False unfolding 2 apply simp
        using t_wf by simp
      note 5 = 3 [unfolded 4]
      have 6: "take (6 + Suc (length t) div 2 * 2)
               (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2 div
               4 ^ (3 + Suc (length t) div 2) * 4 ^ (3 + Suc (length t) div 2))) =
               replicate (6 + Suc (length t) div 2 * 2) False"
        by (metis 2 False div_greater_zero_iff nat_le_linear take_mult_pow2
            zero_less_numeral zero_less_power)
      obtain k :: nat where k_def: "next_square
          ((rev (flatten t) @ [False, True, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
          4 ^ (3 + Suc (length t) div 2)) =
          (rev (flatten t) @ [False, True, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
          4 ^ (3 + Suc (length t) div 2) + k"
        using nat_le_iff_add next_sq_correct2 by presburger
      have 7: "(rev (flatten t) @ [False, True, True])\<^sub>2 \<ge> 2 ^ (6 + Suc (length t) div 2 * 2)"
        using 2 False by linarith
      have 8: "length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2
               div 2 ^ (6 + Suc (length t) div 2 * 2) *
               2 ^ (6 + Suc (length t) div 2 * 2))) = 2 * length t + 3"
        apply (subst bit_length_div_mult_eq')
         apply fact
        apply (subst bin_nat_bin)
         apply simp
        using t_wf by simp
      have 9: "(2::nat) ^ (4 + (length (bin_of_nat ((rev (flatten t) @ [False, True, True])\<^sub>2
               div 2 ^ (6 + Suc (length t) div 2 * 2) *
               2 ^ (6 + Suc (length t) div 2 * 2))) - Suc 0) div 2) \<le>
               2 ^ (6 + Suc (length t) div 2 * 2)" by (simp add: 8)
      have 10: "bit_length (next_square
          ((rev (flatten t) @ [False, True, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
          4 ^ (3 + Suc (length t) div 2))) =
          bit_length (((rev (flatten t) @ [False, True, True])\<^sub>2 div
          4 ^ (3 + Suc (length t) div 2) * 4 ^ (3 + Suc (length t) div 2)))"
        unfolding k_def unfolding 2
        apply (subst (2 5) mult.commute)
        apply (subst bit_length_pow2_mult_add)
        using k_def next_sq_diff [of "(rev (flatten t) @ [False, True, True])\<^sub>2 div
          4 ^ (3 + Suc (length t) div 2) * 4 ^ (3 + Suc (length t) div 2)"] unfolding 2
          apply (simp del: next_sq_def)
        using 9 apply linarith
        using 7 div_greater_zero_iff apply presburger
        by (metis 7 bit_length_mult_pow2 div_greater_zero_iff minus_mod_eq_div_mult
            minus_mod_eq_mult_div nat_zero_less_power_iff pos2)
      have 11: "bit_length (((rev (flatten t) @ [False, True, True])\<^sub>2 div
               4 ^ (3 + Suc (length t) div 2) * 4 ^ (3 + Suc (length t) div 2))) =
              3 + 2 * length t"
        unfolding 2 apply (subst bit_length_div_mult_eq)
        using False unfolding 2 apply simp
        using t_wf by simp
      show "length (bij_bin_bin' (butlast (bin_of_nat (next_square
          ((rev (flatten t) @ [False, True, True])\<^sub>2 div 4 ^ (3 + Suc (length t) div 2) *
          4 ^ (3 + Suc (length t) div 2)))))) \<le> Suc (Suc (2 * length t))"
        using 10 unfolding 11 by (metis (no_types, lifting) Nat.add_diff_assoc2 add_2_eq_Suc
            add_diff_cancel_left' length_bij_bin_bin'_upper_bound length_butlast
            numeral_2_eq_2 numeral_3_eq_3 one_le_numeral plus_1_eq_Suc)
    qed
  qed
next
  case (6 t)
  hence t_wf: "bin'_wf t" by fastforce
  have 1: "butlast (rev (flatten t) @ [True, True]) = rev (flatten t) @ [True]"
    by (simp add: butlast_append)
  have 2: "(4::nat) ^ (3 + Suc (length t) div 2) = 2 ^ (6 + Suc (length t) div 2 * 2)"
    by (metis (no_types, lifting) mult_2_right numeral_Bit0 power_add power_mult_distrib)
  obtain k :: nat where k_def: "next_square ((rev (flatten t) @ [True, True])\<^sub>2 div
                                2 ^ (6 + Suc (length t) div 2 * 2) *
                                2 ^ (6 + Suc (length t) div 2 * 2)) =
                                (rev (flatten t) @ [True, True])\<^sub>2 div
                                2 ^ (6 + Suc (length t) div 2 * 2) *
                                2 ^ (6 + Suc (length t) div 2 * 2) + k"
    using le_Suc_ex next_sq_correct2 by presburger
  show ?case using t_wf unfolding adj_square'_def gn'_defs gn_defs suffix'_len_def
    apply (simp del: next_sq_def add: 1 2)
    unfolding minus_mod_eq_div_mult k_def
  proof (cases "(rev (flatten t) @ [True, True])\<^sub>2 \<ge> 2 ^ (6 + Suc (length t) div 2 * 2)")
    case True
    have 3: "(2::nat) ^ (4 + (length (bin_of_nat
           ((rev (flatten t) @ [True, True])\<^sub>2 div 2 ^ (6 + Suc (length t) div 2 * 2) *
           2 ^ (6 + Suc (length t) div 2 * 2))) - 1) div 2) \<le>
           2 ^ (6 + Suc (length t) div 2 * 2)" apply simp
      apply (subst bit_length_div_mult_eq')
       apply fact
      apply simp
      by (simp add: t_wf)
    have 4: "k < 2 ^ (6 + Suc (length t) div 2 * 2)"
      using next_sq_diff [where n="(rev (flatten t) @ [True, True])\<^sub>2 div
                              2 ^ (6 + Suc (length t) div 2 * 2) *
                              2 ^ (6 + Suc (length t) div 2 * 2)"] 3
      by (smt (verit, ccfv_SIG) diff_add_inverse k_def order_less_le_trans)
    have [simp]: "length (flatten t) = 2 * length t" using t_wf by simp
    show "length (bij_bin_bin' (butlast (bin_of_nat
          ((rev (flatten t) @ [True, True])\<^sub>2 div 2 ^ (6 + Suc (length t) div 2 * 2) *
          2 ^ (6 + Suc (length t) div 2 * 2) + k)))) \<le> Suc (Suc (2 * length t))"
    proof (cases "6 + Suc (length t) div 2 * 2 < 2 * length t")
      case 1: True
      have 5: "bit_length ((rev (flatten t) @ [True, True])\<^sub>2 div
             2 ^ (6 + Suc (length t) div 2 * 2) * 2 ^ (6 + Suc (length t) div 2 * 2) + k) =
             2 * length t + 2"
      apply (subst (2) mult.commute)
      apply (subst bit_length_pow2_mult_add)
        apply fact
       apply auto
      using True div_greater_zero_iff apply presburger
      unfolding bin_of_nat_div_pow2 apply simp
      using 1 by simp
      show ?thesis using 5
        by (metis (no_types, lifting) add_2_eq_Suc' add_diff_cancel_left' le_SucI
            length_bij_bin_bin'_upper_bound length_butlast plus_1_eq_Suc)
    next
      case False
      then show ?thesis
      proof (cases "6 + Suc (length t) div 2 * 2 \<le> 2 * length t + 1")
        case True
        hence "6 + Suc (length t) div 2 * 2 = 2 * length t \<or>
               6 + Suc (length t) div 2 * 2 = 2 * length t + 1" using False by linarith
        moreover have "6 + Suc (length t) div 2 * 2 = 2 * length t \<Longrightarrow> ?thesis"
        proof simp
          assume a1: "6 + Suc (length t) div 2 * 2 = 2 * length t"
          have "bin_of_nat ((rev (flatten t) @ [True, True])\<^sub>2 div
                (2 ^ (2 * length t))) = [True, True]"
            unfolding bin_of_nat_div_pow2 by simp
          hence 1: "(rev (flatten t) @ [True, True])\<^sub>2 div (2 ^ (2 * length t)) = 3"
            by (metis One_nat_def adj_sq_nat bin'_repl nat_bin_nat nat_of_bin_all_True
                numeral_1_eq_Suc_0 numeral_2_eq_2 numeral_Bit1_eq_inc_double one_power2
                plus_1_eq_Suc)
          have 2: "(3::nat) * 2^(2 * length t) = 2^(Suc (2 * length t)) + 2^(2 * length t)"
            by simp
          have 3: "bit_length (2 ^ Suc (2 * length t) + (2 ^ (2 * length t) + k)) =
                   Suc (Suc (2 * length t))"
            apply (subst bit_length_pow2_add)
             apply auto
            using 4 a1 by simp
          show "length (bij_bin_bin' (butlast (bin_of_nat
                ((rev (flatten t) @ [True, True])\<^sub>2 div 2 ^ (2 * length t) *
                2 ^ (2 * length t) + k)))) \<le> Suc (Suc (2 * length t))"
            unfolding 1 2 using 3
            by (metis (no_types, lifting) One_nat_def diff_Suc_1' group_cancel.add1
                le_imp_less_Suc length_bij_bin_bin'_upper_bound length_butlast
                less_imp_le_nat)
        qed
        moreover have "6 + Suc (length t) div 2 * 2 = 2 * length t + 1 \<Longrightarrow> ?thesis"
          apply (erule ssubst)
        proof auto
          have "bin_of_nat ((rev (flatten t) @ [True, True])\<^sub>2 div
                (2 ^ (Suc (2 * length t)))) = [True]"
            unfolding bin_of_nat_div_pow2 by simp
          hence 1: "(rev (flatten t) @ [True, True])\<^sub>2 div (2 ^ (Suc (2 * length t))) = 1"
            by (metis Binary.inc.simps(1) One_nat_def inc_Suc nat_bin_nat
                nat_of_bin.simps(1))
          show "length (bij_bin_bin' (butlast (bin_of_nat
                ((rev (flatten t) @ [True, True])\<^sub>2 div (2 * 2 ^ (2 * length t)) *
                (2 * 2 ^ (2 * length t)) + k)))) \<le> Suc (Suc (2 * length t))"
            unfolding 1 [simplified] apply simp
            by (smt (verit) 4 add.commute add_diff_cancel_left' bit_length_pow2_add
                calculation(1) le_SucI length_bij_bin_bin'_upper_bound
                length_bin_of_nat_pow2 length_butlast plus_1_eq_Suc pos2 power_Suc
                suffix_len_eq)
        qed
        ultimately show ?thesis ..
      next
        case 2: False
        then show ?thesis using False apply simp
          by (smt (z3) 4 One_nat_def Suc_pred True \<open>length (flatten t) = 2 * length t\<close>
              add_2_eq_Suc' bit_len_gt_0_iff bit_length_div_mult_eq' div_greater_zero_iff
              le_trans len_bin_nat_bin length_Cons length_append
              length_bij_bin_bin'_upper_bound length_butlast length_rev list.size(3)
              nat_0_less_mult_iff nat_le_linear not_less_eq_eq numeral_2_eq_2
              pos2 suffix_len_eq zero_less_power)
      qed
    qed
  next
    case False
    then show "length (bij_bin_bin' (butlast (bin_of_nat
               ((rev (flatten t) @ [True, True])\<^sub>2 div 2 ^ (6 + Suc (length t) div 2 * 2) *
               2 ^ (6 + Suc (length t) div 2 * 2) + k)))) \<le> Suc (Suc (2 * length t))"
      using k_def by auto
  qed
next
  case (7 t)
  hence t_wf: "bin'_wf t" by fastforce
  have [simp]: "butlast (rev (flatten t) @ [True, True, True]) =
                rev (flatten t) @ [True, True]" by (simp add: butlast_append)
  have [simp]: "length (bij_bin_bin' (rev (flatten t) @ [True, True])) = Suc (length t)"
    by (simp add: eT_length_bij_bin_bin' t_wf)
  have 1: "(4::nat) ^ (3 + Suc (length t) div 2) = 2 ^ (6 + Suc (length t) div 2 * 2)"
    by (metis (no_types, lifting) mult_2_right numeral_Bit0 power_add power_mult_distrib)
  obtain k :: nat where k_def: "next_square (2 ^ (6 + Suc (length t) div 2 * 2) *
                                ((rev (flatten t) @ [True, True, True])\<^sub>2 div
                                2 ^ (6 + Suc (length t) div 2 * 2))) =
                                2 ^ (6 + Suc (length t) div 2 * 2) *
                                ((rev (flatten t) @ [True, True, True])\<^sub>2 div
                                2 ^ (6 + Suc (length t) div 2 * 2)) + k"
    using nat_le_iff_add next_sq_correct2 by presburger
  have "(2::nat) ^ (4 + (length (bin_of_nat (2 ^ (6 + Suc (length t) div 2 * 2) *
        ((rev (flatten t) @ [True, True, True])\<^sub>2 div 2 ^ (6 + Suc (length t) div 2 * 2)))) -
        1) div 2) \<le> 2 ^ (6 + Suc (length t) div 2 * 2)" apply simp
  proof (cases "2 ^ (6 + Suc (length t) div 2 * 2) \<le>
                (rev (flatten t) @ [True, True, True])\<^sub>2")
    case True
    then show "(length (bin_of_nat (2 ^ (6 + Suc (length t) div 2 * 2) *
               ((rev (flatten t) @ [True, True, True])\<^sub>2 div
               2 ^ (6 + Suc (length t) div 2 * 2)))) - Suc 0) div 2
               \<le> Suc (Suc (Suc (length t) div 2 * 2))"
      apply (subst (2) mult.commute)
      apply (subst bit_length_div_mult_eq')
       apply auto
      using t_wf by simp
  next
    case False
    then show "(length (bin_of_nat (2 ^ (6 + Suc (length t) div 2 * 2) *
               ((rev (flatten t) @ [True, True, True])\<^sub>2 div
               2 ^ (6 + Suc (length t) div 2 * 2)))) - Suc 0) div 2
               \<le> Suc (Suc (Suc (length t) div 2 * 2))" by simp
  qed
  hence 2: "k < 2 ^ (6 + Suc (length t) div 2 * 2)"
    using next_sq_diff [where n="2 ^ (6 + Suc (length t) div 2 * 2) *
                              ((rev (flatten t) @ [True, True, True])\<^sub>2 div
                              2 ^ (6 + Suc (length t) div 2 * 2))"]
    by (smt (verit, best) add_diff_cancel_left' k_def le_add_diff_inverse trans_less_add1)
  show ?case using t_wf unfolding adj_square'_def gn'_defs gn_defs suffix'_len_def
    apply (simp del: next_sq_def add: minus_mod_eq_mult_div add: 1 k_def)
  proof (cases "2 ^ (6 + Suc (length t) div 2 * 2) \<le>
                (rev (flatten t) @ [True, True, True])\<^sub>2")
    case True
    have [simp]: "length (flatten t) = 2 * length t" using t_wf by simp
    have 3: "bit_length (2 ^ (6 + Suc (length t) div 2 * 2) * ((rev (flatten t) @
             [True, True, True])\<^sub>2 div 2 ^ (6 + Suc (length t) div 2 * 2)) + k) =
             2 * length t + 3"
      apply (subst bit_length_pow2_mult_add)
        apply fact
       apply auto
      using True div_greater_zero_iff apply presburger
      unfolding bin_of_nat_div_pow2 apply simp
    proof (cases "6 + Suc (length t) div 2 * 2 < 2 * length t")
      case True
      then show "3 + (2 * length t - (6 + Suc (length t) div 2 * 2) +
                 (Suc (Suc (Suc 0)) - (6 + Suc (length t) div 2 * 2 - 2 * length t)) +
                 Suc (length t) div 2 * 2) = 2 * length t" by simp
    next
      case False
      then show "3 + (2 * length t - (6 + Suc (length t) div 2 * 2) +
                 (Suc (Suc (Suc 0)) - (6 + Suc (length t) div 2 * 2 - 2 * length t)) +
                 Suc (length t) div 2 * 2) = 2 * length t" apply simp
      proof (cases "3 + Suc (length t) div 2 * 2 < 2 * length t")
        case True
        then show "3 + (2 * length t - (3 + Suc (length t) div 2 * 2) +
                   Suc (length t) div 2 * 2) = 2 * length t" by simp
      next
        case False
        hence 1: "3 + Suc (length t) div 2 * 2 \<ge> 2 * length t" by simp
        then show "3 + (2 * length t - (3 + Suc (length t) div 2 * 2) +
                   Suc (length t) div 2 * 2) = 2 * length t"
          using True
        proof simp
          assume a1: "2 * length t \<le> 3 + Suc (length t) div 2 * 2" and
                 a2: "2 ^ (6 + Suc (length t) div 2 * 2) \<le>
                      (rev (flatten t) @ [True, True, True])\<^sub>2"
          have "length t \<le> 3" using a1 by presburger
          moreover have "length t = 0 \<Longrightarrow> 3 + Suc (length t) div 2 * 2 = 2 * length t"
            using a2 by simp
          moreover have "length t = 1 \<Longrightarrow> 3 + Suc (length t) div 2 * 2 = 2 * length t"
            using a2 apply simp
            unfolding length_1_ex1_iff
          proof auto
            fix x :: bin
            assume a1: "256 \<le> (rev x @ [True, True, True])\<^sub>2" and a2: "t = [x]"
            have "x = [False, False] \<or> x = [False, True] \<or> x = [True, False] \<or>
                  x = [True, True]" using a2 t_wf by auto
            moreover have "x = [False, False] \<Longrightarrow> False" using a1 by simp
            moreover have "x = [False, True] \<Longrightarrow> False" using a1 by simp
            moreover have "x = [True, False] \<Longrightarrow> False" using a1 by simp
            moreover have "x = [True, True] \<Longrightarrow> False" using a1 by simp
            ultimately show False by blast
          qed
          moreover have "length t = 2 \<Longrightarrow> 3 + Suc (length t) div 2 * 2 = 2 * length t"
            using a2 apply simp
            unfolding length_2_ex_iff
          proof auto
            fix x y :: bin
            assume a1: "256 \<le> (rev y @ rev x @ [True, True, True])\<^sub>2" and a2: "t = [x, y]"
            have 1: "x = [False, False] \<or> x = [False, True] \<or> x = [True, False] \<or>
                     x = [True, True]" using a2 t_wf by fastforce
            have 2: "y = [False, False] \<or> y = [False, True] \<or> y = [True, False] \<or>
                     y = [True, True]" using a2 t_wf by fastforce
            show False using 1 2 a1 by auto
          qed
          moreover have "length t = 3 \<Longrightarrow> 3 + Suc (length t) div 2 * 2 = 2 * length t"
            using a2
          proof simp
            assume a1: "length t = 3" and
                   a2: "1024 \<le> (rev (flatten t) @ [True, True, True])\<^sub>2"
            then obtain x y z :: bin where t_def: "t = [x, y, z]"
              by (metis length_2_ex_iff length_Suc_conv numeral_2_eq_2 numeral_3_eq_3)
            have "x = [False, False] \<or> x = [False, True] \<or> x = [True, False] \<or>
                  x = [True, True]" using t_def t_wf by fastforce
            moreover have "y = [False, False] \<or> y = [False, True] \<or> y = [True, False] \<or>
                           y = [True, True]" using t_def t_wf by fastforce
            moreover have "z = [False, False] \<or> z = [False, True] \<or> z = [True, False] \<or>
                           z = [True, True]" using t_def t_wf by fastforce
            ultimately show False using a2 by (auto simp add: t_def)
          qed
          ultimately show "3 + Suc (length t) div 2 * 2 = 2 * length t" by linarith
        qed
      qed
    qed
    show "length (bij_bin_bin' (butlast (bin_of_nat
          (2 ^ (6 + Suc (length t) div 2 * 2) * ((rev (flatten t) @
          [True, True, True])\<^sub>2 div 2 ^ (6 + Suc (length t) div 2 * 2)) + k))))
          \<le> Suc (Suc (2 * length t))" using 3
      by (smt (z3) \<open>butlast (rev (flatten t) @ [True, True, True]) =
          rev (flatten t) @ [True, True]\<close> add_2_eq_Suc' bin'_wf_length length_Cons
          length_append length_bij_bin_bin'_upper_bound length_butlast length_rev
          list.size(3) numeral_2_eq_2 numeral_3_eq_3 t_wf)
  next
    case False
    then show "length (bij_bin_bin' (butlast (bin_of_nat
               (2 ^ (6 + Suc (length t) div 2 * 2) * ((rev (flatten t) @
               [True, True, True])\<^sub>2 div 2 ^ (6 + Suc (length t) div 2 * 2)) + k))))
               \<le> Suc (Suc (2 * length t))" apply simp
      using k_def by force
  qed
next
  case (8 b1 b2 b3 t' t)
  then show ?case by fastforce
qed

(* Used in lemma L\<^sub>0 \<notin> DTIME t (file L0.thy) *)
lemma adj_sq_sTw: "length w \<ge> 12 \<Longrightarrow> set w \<subseteq> {w. length w = 2} \<Longrightarrow>
                   gn' ([True, False] # ys) = x\<^sup>2 \<Longrightarrow>
                   adj_sq\<^sub>w' w = [True, False] # ys \<Longrightarrow> \<exists>ys. w = [True, False] # ys"
proof (auto simp add: adj_square'_def gn'_defs gn_defs suffix'_len_def simp del: next_sq_def)
  assume a1: "set w \<subseteq> {w. length w = 2}" and
         a2: "(rev (flatten ys) @ [False, True, True])\<^sub>2 = x\<^sup>2" and
         a3: "bij_bin_bin' (butlast (bin_of_nat (next_square ((bij_bin'_bin w @ [True])\<^sub>2 -
              (bij_bin'_bin w @ [True])\<^sub>2 mod
              4 ^ (3 + length (bij_bin_bin' (bij_bin'_bin w)) div 2))))) =
              [True, False] # ys" and a4: "12 \<le> length w"
  have [simp]: "bij_bin_bin' (bij_bin'_bin w) = w"
    apply (subst bij_bin_bin'_bin)
    using a1 bin'_wf_def by auto
  have 1: "bij_bin_bin' (butlast (bin_of_nat (next_square ((bij_bin'_bin w @ [True])\<^sub>2 -
           (bij_bin'_bin w @ [True])\<^sub>2 mod 4 ^ (3 + length w div 2))))) = [True, False] # ys"
    using a3 by (simp del: next_sq_def)
  have 2: "(4::nat) ^ (3 + length w div 2) = 2 ^ (6 + length w div 2 * 2)"
    by (metis (no_types, lifting) distrib_left_numeral mult.commute numeral_Bit0_eq_double
        power2_eq_square power_mult)
  note 3 = 1 [unfolded minus_mod_eq_div_mult 2]
  obtain k :: nat where k_def: "next_square ((bij_bin'_bin w @ [True])\<^sub>2 div
                                2 ^ (6 + length w div 2 * 2) *
                                2 ^ (6 + length w div 2 * 2)) =
                                (bij_bin'_bin w @ [True])\<^sub>2 div
                                2 ^ (6 + length w div 2 * 2) *
                                2 ^ (6 + length w div 2 * 2) + k"
    using nat_le_iff_add next_sq_correct2 by presburger
  note 4 = 3 [unfolded k_def]
  have 5: "length (bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
           2 ^ (6 + length w div 2 * 2))) = bit_length ((bij_bin'_bin w @ [True])\<^sub>2)"
    by (smt (z3) 4 Binary.inc.simps(1) One_nat_def add.commute add_diff_cancel_left'
        add_leE bin_of_nat.simps(2) bit_len_gt_0_iff bit_length_div_mult_eq' diff_is_0_eq'
        div_greater_zero_iff k_def le_numeral_extra(4) length_Cons
        length_bij_bin_bin'_upper_bound length_butlast length_greater_0_conv
        nat_0_less_mult_iff nat_bin_nat nat_of_bin.simps(1) next_sq_def one_power2
        plus_1_eq_Suc floor_sqrt_zero zero_less_one)
  have 6: "bin'_wf w"
    using a1 set_all_length_2_wf by auto
  have ys_wf: "bin'_wf ys" by (metis a3 bij_bin_bin'_wf bin'_wf_ConsD)
  have 7 [simplified]: "butlast (bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 div
                        2 ^ (6 + length w div 2 * 2) *
                        2 ^ (6 + length w div 2 * 2) + k)) =
                        bij_bin'_bin ([True, False] # ys)"
    using 4 by (metis bij_bin'_bin_bin')
  have 8: "\<exists>b. bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
           2 ^ (6 + length w div 2 * 2) + k) = (rev (flatten ys) @ [False, True])@[b]"
    using 7 by (metis gn_inv_def gn_inv_of_bin k_def next_sq_gt0)
  have 9: "\<exists>b. bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
           2 ^ (6 + length w div 2 * 2) + k) = rev (flatten ys) @ [False, True, b]"
    using 8 by simp
  hence 10: "bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
             2 ^ (6 + length w div 2 * 2) + k) = rev (flatten ys) @ [False, True, True]"
    apply auto using bin_of_nat_end_True [of "(bij_bin'_bin w @ [True])\<^sub>2 div
           2 ^ (6 + length w div 2 * 2) * 2 ^ (6 + length w div 2 * 2) + k"] apply auto
    by (metis add.right_neutral gr0I k_def mult_is_0 next_sq_gt0)
  have "length (bij_bin'_bin w @ [True]) \<ge> 7 + length w div 2 * 2"
    apply auto
    by (metis 5 Nil_is_append_conv bin_nat_bin bit_len_eq_0_iff div_less length_0_conv
        length_append_singleton length_bin_of_nat_le_iff mult_is_0 not_less_eq_eq)
  hence 11: "(bij_bin'_bin w @ [True])\<^sub>2 \<ge> 2 ^ (6 + length w div 2 * 2)" apply auto
    by (metis Nil_is_append_conv bit_len_eq_0_iff div_less leI length_0_conv
        length_bin_of_nat_mod minus_mod_eq_div_mult mult_is_0 not_Cons_self2)
  note next_sq_diff [of "(bij_bin'_bin w @ [True])\<^sub>2 div
                         2 ^ (6 + length w div 2 * 2) * 2 ^ (6 + length w div 2 * 2)"]
  have 12: "length (bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
            2 ^ (6 + length w div 2 * 2))) - 1 = length (bij_bin'_bin w)"
    apply (subst bit_length_div_mult_eq)
     apply fact
    by simp
  note next_sq_diff [of "(bij_bin'_bin w @ [True])\<^sub>2 div
                                2 ^ (6 + length w div 2 * 2) *
                                2 ^ (6 + length w div 2 * 2)", unfolded 12]
  hence 13: "k < 2 ^ (4 + length (bij_bin'_bin w) div 2)" using k_def by linarith
  hence 14: "bit_length k \<le> 4 + length (bij_bin'_bin w) div 2"
    using length_bin_of_nat_le_iff by blast
  have "6 + length w div 2 * 2 \<ge> 4 + length (bij_bin'_bin w) div 2"
    apply auto
    by (metis \<open>bij_bin_bin' (bij_bin'_bin w) = w\<close> add.commute le_SucI
        length_bij_bin_bin'_lower_bound mult.commute odd_two_times_div_two_succ
        plus_1_eq_Suc x_d2_m2_iff2)
  hence 15: "k < 2 ^ (6 + length w div 2 * 2)" using 13
    by (meson le_trans length_bin_of_nat_le_iff)
  have 16: "bin'_wf ys" by (metis a3 bij_bin_bin'_wf bin'_wf_ConsD)
  have 17: "length (bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
            2 ^ (6 + length w div 2 * 2) + k)) = Suc (length (bij_bin'_bin w))"
    apply (subst (2) mult.commute)
    apply (subst bit_length_pow2_mult_add)
      apply fact
    using 11 div_greater_zero_iff apply presburger
    apply (simp add: bin_of_nat_div_pow2)
    apply (cases "length (bij_bin'_bin w) - (6 + length w div 2 * 2) = 0")
     apply auto
    apply (cases "length (bij_bin'_bin w) \<ge> (5 + length w div 2 * 2)")
     apply auto
    by (metis 11 12 5 Suc_leD Suc_nat_number_of_add diff_Suc_1 diff_le_mono
        length_bin_of_bin_leI length_bin_of_nat_pow2 semiring_norm(5) semiring_norm(8))
  have 18: "2 * length ys = length (bij_bin'_bin w) - 2"
    using 10 [THEN arg_cong, of length, simplified] unfolding 17 by (simp add: 16)
  have "length (bij_bin'_bin w) \<ge> 12"
    using a4 6 le_trans length_bij_bin'_bin_ge by blast
  hence "4 + length (bij_bin'_bin w) div 2 \<le> length (bij_bin'_bin w) - 2" by simp
  hence 19: "bit_length k \<le> 2 * length ys" unfolding 18 using 14 le_trans by blast
  have "bin_of_nat (((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
        2 ^ (6 + length w div 2 * 2) + k) div 2 ^ (2 * length ys)) =
        drop (2 * length ys) ((replicate (6 + length w div 2 * 2) False)@
        (drop (6 + length w div 2 * 2) (bij_bin'_bin w @ [True])))"
    apply (subst div_pow2_summand_vanish)
    using 15 length_bin_of_nat_le_iff apply blast
    using 19 apply blast
    apply simp
    unfolding bin_of_nat_div_pow2 apply (subst bin_of_nat_app_0s)
    using 11 div_greater_zero_iff apply presburger
    by (simp add: bin_of_nat_div_pow2)
  hence "bin_of_nat (((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
         2 ^ (6 + length w div 2 * 2) + k) div 2 ^ (2 * length ys)) =
         drop (2 * length ys) (rev (flatten ys) @ [False, True, True])"
    using 10 by (metis bin_of_nat_div_pow2)
  also have "... = [False, True, True]" using ys_wf by simp
  finally have 20: "bin_of_nat (((bij_bin'_bin w @ [True])\<^sub>2 div
                    2 ^ (6 + length w div 2 * 2) *
                    2 ^ (6 + length w div 2 * 2) + k) div 2 ^ (2 * length ys)) =
                    [False, True, True]" .
  have "bin_of_nat (((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
        2 ^ (6 + length w div 2 * 2) + k) div 2 ^ (2 * length ys)) =
        bin_of_nat (((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
        2 ^ (6 + length w div 2 * 2)) div 2 ^ (2 * length ys))"
    apply (subst div_pow2_summand_vanish)
    using 15 length_bin_of_nat_le_iff apply blast
    using 19 by blast standard
  hence "bin_of_nat (((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
         2 ^ (6 + length w div 2 * 2)) div 2 ^ (2 * length ys)) = [False, True, True]"
    using 20 by (simp only:)
  then obtain zs :: bin where zs_def: "bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 div
         2 ^ (6 + length w div 2 * 2) * 2 ^ (6 + length w div 2 * 2)) =
         zs @ [False, True, True]" unfolding bin_of_nat_div_pow2
    using append_take_drop_id [of "2 * length ys" "(bin_of_nat
       ((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
        2 ^ (6 + length w div 2 * 2)))"] by metis
  have 21: "length zs = 2 * length ys"
    by (metis 10 11 15 add_right_cancel bin'_wf_length div_greater_zero_iff
        length_append length_rev nat_zero_less_power_iff pos2 suffix_len_eq ys_wf zs_def)
  have 22: "6 + length w div 2 * 2 \<le> Suc (Suc (2 * length ys))"
    unfolding 18 by (smt (verit) 12 ExtBinary.lengths_le Nitpick.size_list_simp(2)
        One_nat_def \<open>7 + length w div 2 * 2 \<le> length (bij_bin'_bin w @ [True])\<close>
        \<open>bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 div 2 ^ (6 + length w div 2 * 2) *
        2 ^ (6 + length w div 2 * 2) div 2 ^ (2 * length ys)) = [False, True, True]\<close>
        ab_semigroup_add_class.add_ac(1) add_gr_0 add_le_cancel_left butlast_snoc
        div_le_dividend length_butlast length_greater_0_conv length_tl list.size(4)
        numeral_3_eq_3 numeral_Bit0 numeral_eq_Suc one_plus_numeral_commute
        order_less_le_trans ordered_cancel_comm_monoid_diff_class.add_diff_inverse
        plus_1_eq_Suc pred_numeral_simps(3) zero_less_numeral)
  have False if "6 + length w div 2 * 2 = Suc (Suc (2 * length ys))"
    using zs_def 21 unfolding that 18
    apply (subst (asm) bin_of_nat_app_0s)
     apply (metis 12 21 \<open>12 \<le> length (bij_bin'_bin w)\<close> add_implies_diff bin_of_nat.simps(1)
        diff_le_self list.size(3) nat_eq_add_iff2 not_numeral_le_zero order_less_le_trans
        that zero_less_iff_neq_zero)
    unfolding bin_of_nat_div_pow2 apply simp
    by (metis append_eq_append_conv length_replicate list.inject replicate_app_Cons_same)
  hence 23: "6 + length w div 2 * 2 \<le> Suc (2 * length ys)" using 22 by fastforce
  have False if "6 + length w div 2 * 2 = Suc (2 * length ys)" using that
    by (metis add_mult_distrib2 double_not_eq_Suc_double mult.commute
        numeral_Bit0_eq_double)
  hence 24: "6 + length w div 2 * 2 \<le> 2 * length ys" using 23 by fastforce
  have "bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 div
        2 ^ (6 + length w div 2 * 2)) =
        (drop (6 + length w div 2 * 2) zs)@[False, True, True]"
    using zs_def 21 24
    by (smt (verit, ccfv_SIG) \<open>bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 div
  2 ^ (6 + length w div 2 * 2) * 2 ^ (6 + length w div 2 * 2) div 2 ^ (2 * length ys)) =
  [False, True, True]\<close> bin_of_nat_div_pow2 diff_is_0_eq' div_mult_self_is_m drop_append
        drop_consumes_first_append leI le_0_eq nless_le pos2 power_eq_0_iff)
  hence "suffix [False, True, True] (bij_bin'_bin w @ [True])"
    by (metis append_take_drop_id bin_nat_bin bin_of_nat_div_pow2 suffixI suffix_appendI)
  hence 25: "suffix [False, True] (bij_bin'_bin w)" by simp
  then obtain a b :: bool and ys' :: bin' where w_def: "w = [a, b]#ys'" using 6
    by (metis bij_bin'_bin.simps(1) bin2_of_bin.cases group_2.simps(1) group_2_flatten_id
        starts_with_flattenD suffix_Nil)
  have 26: "prefix [[True, False]] (bij_bin_bin' (bij_bin'_bin w))"
  proof -
    have 1: "bij_bin'_bin w = ((take (length (bij_bin'_bin w) - 2) (bij_bin'_bin w)) @
             [False])@[True]" using 25 apply simp
      by (metis append_take_drop_id numeral_2_eq_2)
    have 2: "even (length (bij_bin'_bin ([True, False]#ys)))"
      apply (rule bij_bin'_bin_even_length)
      by fact
    have "even (length (butlast (bin_of_nat (next_square ((bij_bin'_bin w @ [True])\<^sub>2 -
          (bij_bin'_bin w @ [True])\<^sub>2 mod
          4 ^ (3 + length (bij_bin_bin' (bij_bin'_bin w)) div 2))))))"
      using 2 a3 by (metis bij_bin'_bin_bin')
    hence "odd (length (bin_of_nat (next_square ((bij_bin'_bin w @ [True])\<^sub>2 -
           (bij_bin'_bin w @ [True])\<^sub>2 mod
           4 ^ (3 + length (bij_bin_bin' (bij_bin'_bin w)) div 2)))))"
      by (metis append_butlast_last_id bit_len_gt_0_iff even_Suc length_append_singleton
          length_greater_0_conv next_sq_gt0)
    hence "odd (length (bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2 -
           (bij_bin'_bin w @ [True])\<^sub>2 mod
           4 ^ (3 + length (bij_bin_bin' (bij_bin'_bin w)) div 2))))"
      by (smt (z3) 21 \<open>bij_bin_bin' (bij_bin'_bin w) = w\<close> add_2_eq_Suc' add_Suc_shift
          add_diff_cancel_left' butlast_snoc diff_is_0_eq even_two_times_div_two leI
          length_Cons length_append length_butlast list.size(3) minus_mod_eq_div_mult
          mod_add_self2 mod_less mod_mult_self4 mult_2_right numeral_2_eq_2 numeral_Bit0
          numerals(1) power_add power_mult_distrib zero_neq_numeral zs_def)
    hence "odd (length (bin_of_nat ((bij_bin'_bin w @ [True])\<^sub>2)))"
      by (metis (no_types, opaque_lifting) 17 2 4 bij_bin'_bin_bin' bin_nat_bin
          butlast_snoc even_Suc length_append_singleton length_butlast)
    hence 3: "even (length (bij_bin'_bin w))" by simp
    show "prefix [[True, False]] (bij_bin_bin' (bij_bin'_bin w))"
      apply (subst 1)
      unfolding bij_bin_bin'.simps apply simp
      using 3 by (simp add: even_group_2_Cons2)
  qed
  thus "\<exists>ys. w = [True, False] # ys" by (simp add: prefix_def)
qed
end
