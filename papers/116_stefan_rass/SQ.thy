theory SQ
  imports Language_Density "Supplementary/Discrete_Log" "Supplementary/Discrete_Sqrt"
    "HOL-Library.Sublist"
begin

subsection\<open>Language of Integer Squares\<close>

(* SQ is an overloaded identifier in the paper *)
definition SQ :: lang \<comment> \<open>the language of non-zero square numbers, represented by binary strings without leading ones.\<close>
  where "SQ \<equiv> {w. \<exists>x. gn w = x ^ 2}"

definition SQ_nat :: "nat set" \<comment> \<open>the analogous set \<open>SQ \<subseteq> \<nat>\<close>, as defined in ch 4.1\<close>
  where "(SQ_nat::nat set) \<equiv> {y. y \<noteq> 0 \<and> (\<exists>x. y = x ^ 2)}"

declare SQ_def[simp] SQ_nat_def[simp]

lemma SQ_nat_zero:
	"insert 0 SQ_nat = {y. \<exists>x. y = x ^ 2}"
	"SQ_nat = {y. \<exists>x. y = x ^ 2} - {0}"
	by auto

(* relating SQ and SQ_nat *)
lemma SQ_SQ_nat:
  shows SQ_nat_vim: "SQ = gn -` SQ_nat"
    and SQ_nat_eq: "SQ = {w. gn w \<in> SQ_nat}"
  unfolding SQ_def SQ_nat_def by simp_all

lemma SQ_nat_im: "SQ_nat = gn ` SQ"
proof (intro subset_antisym subsetI image_eqI CollectI)
  fix n assume "n \<in> SQ_nat"
  then have "n > 0" by simp
  with sym inv_gn_id show "n = gn (gn_inv n)" .
  from \<open>n \<in> SQ_nat\<close> have "\<exists>x. n = x ^ 2" by simp
  then obtain x where b: "n = x ^ 2" ..
  then show "gn_inv n \<in> SQ" unfolding SQ_def
    by (intro image_eqI CollectI exI) (fold \<open>n = gn (gn_inv n)\<close>)
next
  fix n
  assume "n \<in> gn ` SQ"
  then have "n > 0" using gn_gt_0 by blast
  from \<open>n \<in> gn ` SQ\<close> have "n \<in> {n. \<exists>x. gn (gn_inv n) = x ^ 2}" using gn_inv_id by fastforce
  then have "\<exists>x. gn (gn_inv n) = x ^ 2" by blast
  then obtain x where "gn (gn_inv n) = x ^ 2" ..
  with \<open>n > 0\<close> have "n = x ^ 2" using inv_gn_id by simp
  with \<open>n > 0\<close> show "n \<in> SQ_nat" by simp
qed


lemma lemma_4_2: "dens SQ x = dsqrt x"
proof -
  have eq: "{w\<in>SQ. gn w \<le> x} = gn_inv ` power2 ` {0<..dsqrt x}"
  proof (intro subset_antisym subsetI image_eqI CollectI conjI)
    fix w
    assume "w \<in> {w \<in> SQ. gn w \<le> x}"
    then have "w \<in> SQ" and "gn w \<le> x" by blast+

    show "w = gn_inv (gn w)" unfolding gn_inv_id ..

    from \<open>w \<in> SQ\<close> obtain z where "gn w = z\<^sup>2" unfolding SQ_def by blast
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
    then show "w \<in> SQ" unfolding SQ_def by blast
    from \<open>gn w = z\<^sup>2\<close> and \<open>z \<le> dsqrt x\<close> show "gn w \<le> x" using le_sqrt_iff by simp
  qed

  have "power2 ` {0<..dsqrt x} \<subseteq> {0<..}" by auto
  with inj_on_subset gn_inv_inj have "inj_on gn_inv (power2 ` {0<..dsqrt x})" .
  with card_image have "dens SQ x = card (power2 ` {0<..dsqrt x})" unfolding dens_def eq .
  also have "\<dots> = card {0<..dsqrt x}" by (intro card_image, unfold inj_on_def) fastforce
  also have "\<dots> = dsqrt x" by simp
  finally show ?thesis .
qed


subsection\<open>Log inequality\<close>

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
  unfolding sqrt_def
  using log_root[of 2 x 2] and pos2 \<open>x > 0\<close> .

corollary log2_sqrt':
  fixes x :: real
  assumes "x > 0"
  shows "log 2 (sqrt x) = (log 2 x) / 2"
  using log2_sqrt and \<open>x > 0\<close> by simp

lemma delta_bitlength:
  assumes "1 \<le> x"
  shows "\<lceil>log 2 (2*\<lceil>sqrt x\<rceil>+1)\<rceil> \<le> 3 + \<lceil>log 2 x\<rceil> / 2"
proof -
  have le1: "\<lceil>x/2\<rceil> \<le> 1 + \<lceil>x\<rceil>/2" by linarith
  have le2: "1 \<le> \<lceil>sqrt x\<rceil>" using \<open>1 \<le> x\<close> by simp
  have le3: "log 2 3 < real 2" using less_powr_iff[of 2 3 2] by force
  have le4: "log 2 (sqrt x) = (log 2 x) / 2" using log2_sqrt'[of x] and \<open>1 \<le> x\<close> by simp

  have "\<lceil>log 2 (2*\<lceil>sqrt x\<rceil>+1)\<rceil> \<le> \<lceil>log 2 (3*\<lceil>sqrt x\<rceil>)\<rceil>" using \<open>1 \<le> x\<close>
  proof (intro ceiling_mono, subst log_le_cancel_iff)
    from \<open>1 \<le> \<lceil>sqrt x\<rceil>\<close> show "0 < real_of_int (2 * \<lceil>sqrt x\<rceil> + 1)" by linarith
  qed simp_all
  also have "\<dots> = \<lceil>(log 2 3) + log 2 \<lceil>sqrt x\<rceil>\<rceil>" using le2 and log_mult[of 2 3 "\<lceil>sqrt x\<rceil>"] by auto
  also have "\<dots> \<le> \<lceil>2 + log 2 \<lceil>sqrt x\<rceil>\<rceil>" using le3 ceiling_mono by (simp add: ceiling_mono)
  also have "\<dots> = 2 + \<lceil>log 2 \<lceil>sqrt x\<rceil>\<rceil>" by linarith
  also have "\<dots> \<le> 2 + \<lceil>\<lceil>log 2 (sqrt x)\<rceil>\<rceil>" using log_ceil_le by (simp add: assms ceiling_le_iff)
  also have "\<dots> = 2 + \<lceil>log 2 (sqrt x)\<rceil>" by simp
  also have "\<dots> = 2 + \<lceil>(log 2 x) / 2\<rceil>" unfolding le4 by (rule refl)
  also have "\<dots> \<le> 3 + \<lceil>log 2 x\<rceil> / 2" using le1 by linarith
  finally show ?thesis by simp
qed


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
qed (* case "x \<le> 0" by *) simp

lemma delta_bitlength2:
  "bit_length (next_square n - n) \<le> 3 + (bit_length n) div 2"
  (is "bit_length ?delta \<le> 3 + (bit_length n) div 2")
proof (cases "n > 0", cases "?delta > 0")
  assume "n > 0" and "?delta > 0"

  have "bit_length ?delta = \<lfloor>log 2 ?delta\<rfloor> + 1" using bit_length_eq_log and \<open>?delta > 0\<close> .
  also have "... \<le> \<lfloor>log 2 (2 * dsqrt n + 1)\<rfloor> + 1"
  proof -
    have "real ?delta \<le> real (2 * dsqrt n + 1)" using next_sq_diff of_nat_le_iff by blast
    then have "log 2 ?delta \<le> log 2 (2 * dsqrt n + 1)"
      using \<open>?delta > 0\<close> by (subst log_le_cancel_iff) simp_all
    then have "\<lfloor>log 2 ?delta\<rfloor> \<le> \<lfloor>log 2 (2 * dsqrt n + 1)\<rfloor>" by (rule floor_mono)
    then show ?thesis by presburger
  qed
  also have "... = \<lfloor>log 2 (2 * \<lfloor>sqrt n\<rfloor> + 1)\<rfloor> + 1"
  proof -
    thm sqrt_altdef sqrt_altdef_nat
    have "real (2 * dsqrt n + 1) = real_of_int (2 * \<lfloor>sqrt n\<rfloor> + 1)" by (fold sqrt_altdef) simp
    then show ?thesis by presburger
  qed
  also have "... \<le> \<lceil>log 2 (2 * \<lceil>sqrt n\<rceil> + 1)\<rceil>" (is "?l + 1 \<le> ?r")
  proof - \<comment> \<open>this follows from \<open>sqrt n\<close> not being an integer, from assumption \<open>?delta > 0\<close>\<close>
    have "?l < ?r" unfolding order.strict_iff_order
    proof (* ?l < ?r \<longleftrightarrow> ?l \<le> ?r \<and> ?l \<noteq> ?r *)
      let ?roi = real_of_int
      from \<open>n > 0\<close> have "?roi \<lfloor>sqrt n\<rfloor> > 0" "?roi \<lceil>sqrt n\<rceil> > 0" by simp_all
      then have h3b: "?roi (2 * \<lfloor>sqrt n\<rfloor> + 1) > 0" "?roi (2 * \<lceil>sqrt n\<rceil> + 1) > 0" by linarith+
      then have h3c: "log 2 (2 * \<lfloor>sqrt n\<rfloor> + 1) \<le> log 2 (2 * \<lceil>sqrt n\<rceil> + 1)" by simp
      then show le: "\<lfloor>log 2 (2 * \<lfloor>sqrt n\<rfloor> + 1)\<rfloor> \<le> \<lceil>log 2 (2 * \<lceil>sqrt n\<rceil> + 1)\<rceil>" by linarith
      show "?l \<noteq> ?r"
      proof
        assume "?l = ?r"
        with h3c have "log 2 (2 * \<lfloor>sqrt n\<rfloor> + 1) = log 2 (2 * \<lceil>sqrt n\<rceil> + 1)" by linarith
        then have "?roi (2 * \<lfloor>sqrt n\<rfloor> + 1) = ?roi (2 * \<lceil>sqrt n\<rceil> + 1)" using log_eq_cancel_iff h3b by simp
        then have "\<lfloor>sqrt n\<rfloor> = \<lceil>sqrt n\<rceil>" by simp
        then have "sqrt n = \<lfloor>sqrt n\<rfloor>" using floor_eq_ceil_nat by blast
        then have "(sqrt n)\<^sup>2 = \<lfloor>sqrt n\<rfloor>\<^sup>2" by simp
        then have "real n = \<lfloor>sqrt n\<rfloor>\<^sup>2" by (subst (asm) real_sqrt_pow2) simp_all
        then have "n = \<lfloor>sqrt n\<rfloor>\<^sup>2" by linarith
        then have "int n = (nat \<lfloor>sqrt n\<rfloor>)\<^sup>2" by simp
        then have "n = (nat \<lfloor>sqrt n\<rfloor>)\<^sup>2" by presburger
        then have "is_square n" ..
        then have "next_square n = n" using next_sq_eq and \<open>n > 0\<close> by blast
        then show False using \<open>?delta > 0\<close> by simp
      qed
    qed
    then show "?l + 1 \<le> ?r" by simp
  qed
  also have "... \<le> 3 + \<lceil>log 2 n\<rceil> div 2"
  proof -
    have "\<lceil>log 2 (2 * \<lceil>sqrt n\<rceil> + 1)\<rceil> = \<lfloor> \<lceil>log 2 (2 * \<lceil>sqrt n\<rceil> + 1)\<rceil> \<rfloor>" unfolding floor_of_int ..
    also have "... \<le> \<lfloor>3 + \<lceil>log 2 n\<rceil> / 2\<rfloor>" using \<open>n > 0\<close> by (intro floor_mono delta_bitlength) simp
    also have "... = 3 + \<lfloor>\<lceil>log 2 n\<rceil> / of_int 2\<rfloor>" by simp
    also have "... = 3 + \<lceil>log 2 n\<rceil> div 2" unfolding add_left_cancel floor_divide_of_int_eq ..
    finally show ?thesis .
  qed
  also have "... \<le> 3 + (\<lfloor>log 2 n\<rfloor> + 1) div 2" using ceil_le_floor_plus1[of "log 2 n"]
    by (intro add_left_mono zdiv_mono1) simp_all
  also have "... = 3 + bit_length n div 2"
    unfolding \<open>n > 0\<close>[THEN bit_length_eq_log, symmetric] of_nat_add of_nat_numeral of_nat_div ..
  finally show ?thesis by (fold zle_int)
qed simp_all \<comment> \<open>cases \<open>n = 0\<close> or \<open>?delta = 0\<close>\<close>


subsection\<open>Length of prefix\<close>

\<comment> \<open>\<open>w'\<close> (next_square n) will eventually have an identical lot of \<open>\<lceil>log l\<rceil>\<close> most significant bits\<close>

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
  also have "... \<le> 2 powr (4 + dlog n div 2)"
  proof -
    have "2 + log 2 (real n) / 2 \<le> 4 + \<lfloor>\<lfloor>log 2 (real n)\<rfloor> / 2\<rfloor>" by linarith
    also have "... = 4 + \<lfloor>log 2 (real n)\<rfloor> div 2"
      unfolding floor_divide_of_int_eq[of _ 2, unfolded of_int_numeral] ..
    also have "... = 4 + dlog n div 2"
    proof -
      from \<open>n > 0\<close> have "n \<noteq> 0" ..
      with log_altdef have *: "\<lfloor>log 2 n\<rfloor> = int (dlog n)" by simp
      then have "4 + \<lfloor>log 2 (real n)\<rfloor> div 2 = (4 + (int (dlog n)) div 2)" unfolding * by blast
      also have "... = 4 + dlog n div 2" unfolding of_nat_add of_nat_numeral of_nat_div ..
      finally have **: "4 + \<lfloor>log 2 n\<rfloor> div 2 = 4 + dlog n div 2" .
      show ?thesis unfolding ** using of_int_of_nat_eq .
    qed
    finally show ?thesis by simp
  qed
  also have "... = 2 ^ (4 + dlog n div 2)" using powr_realpow[of 2] by fastforce
  finally have "real (2 * dsqrt n + 1) < real (2 ^ (4 + dlog n div 2))" by simp
  then have "2 * dsqrt n + 1 < 2 ^ (4 + dlog n div 2)" unfolding of_nat_less_iff .

  also have "... \<le> 2 ^ (4 + bit_length n div 2)" using \<open>n > 0\<close> by (subst bit_len_eq_dlog) simp_all
  finally show ?thesis .
qed (* case "n = 0" by *) simp

lemma adj_sq_diff: "next_square n - prev_square n < 2 ^ (4 + bit_length n div 2)"
  using adj_sq_diff_pow2 next_prev_sq_diff by (rule dual_order.strict_trans2)

lemma next_sq_diff: "next_square n - n < 2 ^ (4 + bit_length n div 2)"
  using adj_sq_diff_pow2 next_sq_diff by (rule dual_order.strict_trans2)


definition suffix_len :: "nat \<Rightarrow> nat"
  where "suffix_len n \<equiv> 4 + bit_length n div 2"

(*
 * Choose the adjacent square of \<open>n\<close> as the \<open>next_square\<close> of the smallest number sharing its prefix.
 * That is, the prefix concatenated with zeroes to have the same length as \<open>n\<close>.
 *)
definition adj_square :: "nat \<Rightarrow> nat"
  where "adj_square n = next_square (n - n mod 2^(suffix_len n))"

declare suffix_len_def[simp] adj_square_def[simp]

lemma adj_sq_gt_0: "adj_square n > 0" unfolding adj_square_def by (rule next_sq_gt0)

lemma adj_sq_correct: "is_square (adj_square n)"
  unfolding adj_square_def using next_sq_correct1 .

lemma adj_sq_correct': "gn_inv (adj_square n) \<in> SQ" unfolding SQ_def
  using adj_sq_gt_0 adj_sq_correct by (intro CollectI) (subst inv_gn_id)

definition bin_prefix :: "bin \<Rightarrow> nat \<Rightarrow> bool"
  where "bin_prefix ps n \<equiv> suffix ps (bin_of_nat n)"

definition shared_bin_prefix :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "shared_bin_prefix l a b = (\<exists>ps. length ps = l \<and> bin_prefix ps a \<and> bin_prefix ps b)"

lemma suffix_length_unique: "suffix ps xs \<Longrightarrow> suffix qs xs \<Longrightarrow> length ps = length qs \<Longrightarrow> ps = qs"
  by (subst suffix_order.eq_iff, intro conjI; subst suffix_length_suffix) simp_all

lemma shared_bin_prefixI[intro]:
  assumes "length ps = l"
    and "bin_prefix ps a"
    and "bin_prefix ps b"
  shows "shared_bin_prefix l a b"
  unfolding shared_bin_prefix_def using assms by blast

lemma shared_bin_prefixI':
  fixes l a b :: nat
  defines "k \<equiv> bit_length a - l"
  defines "ps \<equiv> drop k (bin_of_nat a)"
  assumes "bit_length a \<ge> l"
    and "bin_prefix ps b"
  shows "shared_bin_prefix l a b"
proof (intro shared_bin_prefixI)
  let ?a = "bin_of_nat a"
  from \<open>bit_length a \<ge> l\<close> show "length ps = l" unfolding ps_def k_def by simp
  show "bin_prefix ps a" unfolding ps_def bin_prefix_def using suffix_drop .
  show "bin_prefix ps b" using \<open>bin_prefix ps b\<close> .
qed

lemma shared_bin_prefixE[elim]:
  assumes "shared_bin_prefix l a b"
  obtains ps where "length ps = l"
    and "bin_prefix ps a"
    and "bin_prefix ps b"
  using assms unfolding shared_bin_prefix_def by blast

lemma shared_bin_max_len1:
  assumes "shared_bin_prefix l a b"
  shows "l \<le> bit_length a"
proof -
  from assms obtain ps
    where psl: "length ps = l"
      and psa: "bin_prefix ps a" ..
  from suffix_length_le[of ps] and psa show ?thesis unfolding bin_prefix_def psl .
qed

lemma shared_bin_max_len2:
  assumes "shared_bin_prefix l a b"
  shows "l \<le> bit_length b"
proof -
  from assms obtain ps
    where psl: "length ps = l"
      and psb: "bin_prefix ps b" ..
  from suffix_length_le[of ps] and psb show ?thesis unfolding bin_prefix_def psl .
qed

lemma shared_bin_prefixE'[elim]:
  assumes ab: "shared_bin_prefix l a b"
  defines "psa \<equiv> drop (bit_length a - l) (bin_of_nat a)"
  defines "psb \<equiv> drop (bit_length b - l) (bin_of_nat b)"
  shows "psa = psb"
    and "length psa = l"
    and "bin_prefix psa a"
    and "bin_prefix psa b"
proof -
  from ab obtain ps'
    where psl': "length ps' = l"
      and psa': "bin_prefix ps' a"
      and psb': "bin_prefix ps' b" ..

  show psa: "bin_prefix psa a" unfolding bin_prefix_def psa_def using suffix_drop .
  have psb: "bin_prefix psb b" unfolding bin_prefix_def psb_def using suffix_drop .

  have "l \<le> bit_length a" using shared_bin_max_len1 \<open>shared_bin_prefix l a b\<close> .
  with diff_diff_cancel show "length psa = l" unfolding psa_def length_drop .
  with psl' have psl: "length ps' = length psa" ..
  with suffix_length_unique psa' psa have psaeq: "ps' = psa" unfolding bin_prefix_def .
  from psb' show "bin_prefix psa b" unfolding psaeq .

  have "l \<le> bit_length b" using shared_bin_max_len2 \<open>shared_bin_prefix l a b\<close> .
  with diff_diff_cancel have "length psb = l" unfolding psb_def length_drop .
  with psl' have psl: "length ps' = length psb" ..
  with suffix_length_unique psb' psb have psbeq: "ps' = psb" unfolding bin_prefix_def .

  show "psa = psb" by (fold psaeq psbeq) rule
qed


(*lemma bit_len_eq_bin_len: "n > 0 \<Longrightarrow> bit_length n = length (bin_of_nat n)" by blast*)

lemma shared_bin_prefix_refl:
  assumes "n > 0"
    and "bit_length n > l"
  shows "shared_bin_prefix l n n"
proof (intro shared_bin_prefixI, tactic distinct_subgoals_tac (* removes duplicate subgoals *))
  let ?ps = "drop (bit_length n - l) (bin_of_nat n)"
  show "length ?ps = l" using assms by fastforce
  show "bin_prefix ?ps n" unfolding bin_prefix_def using suffix_drop by blast
qed

lemma shared_bin_prefix_trans:
  assumes "a > 0" "b > 0" "c > 0"
  assumes ab: "shared_bin_prefix l a b"
    and bc: "shared_bin_prefix l b c"
  shows "shared_bin_prefix l a c"
proof (intro shared_bin_prefixI)
  define ps where "ps \<equiv> drop (bit_length a - l) (bin_of_nat a)"
  show ps_a: "bin_prefix ps a" unfolding ps_def bin_prefix_def using suffix_drop .

  from ab obtain ps_ab where ab_l: "length ps_ab = l"
    and ab_a: "bin_prefix ps_ab a" and ab_b: "bin_prefix ps_ab b" ..
  from bc obtain ps_bc where bc_l: "length ps_bc = l"
    and bc_b: "bin_prefix ps_bc b" and bc_c: "bin_prefix ps_bc c" ..

  have "l \<le> length (bin_of_nat a)"
    using suffix_length_le[of ps_ab] ab_a unfolding bin_prefix_def ab_l .
  with diff_diff_cancel show ps_l: "length ps = l" unfolding ps_def length_drop .

  from trans_sym ps_l have "length ps = length ps_ab" using ab_l .
  with suffix_length_unique ps_a ab_a have ab_eq: "ps = ps_ab" unfolding bin_prefix_def .
  from trans_sym ps_l have "length ps = length ps_bc" using bc_l .
  with suffix_length_unique ab_b bc_b have bc_eq: "ps = ps_bc" unfolding bin_prefix_def ab_eq .

  show "bin_prefix ps c" unfolding bc_eq using bc_c .
qed

lemma add_suffix_bin:
  fixes up lo k :: nat
  assumes "lo < 2^k"
  shows "up * 2^k + lo = nat_of_bin ((bin_of_nat lo) @ (replicate (k - (length (bin_of_nat lo))) False) @ (bin_of_nat up))"
    (is "?lhs = nat_of_bin (?lo @ ?zs @ ?up)")
proof (cases "up > 0", cases "lo > 0")
  assume "up > 0" and "lo > 0"
  let ?n = nat_of_bin
    and ?b = bin_of_nat
    and ?z = "\<lambda>l. replicate l False"

  have "k > 0" using \<open>lo < 2^k\<close> \<open>lo > 0\<close> by (cases "k > 0") force+

  from \<open>lo < 2^k\<close> have "lo \<le> 2 ^ k - 1" by simp
  with log_le_iff have dllo: "dlog lo \<le> dlog (2^k - 1)" .

  have "bit_length lo = dlog lo + 1" using bit_len_eq_dlog \<open>lo > 0\<close> .
  also have "... \<le> dlog (2^k - 1) + 1" using add_right_mono dllo .
  also have "... = k - 1 + 1" using arg_cong log_exp_m1 .
  also have "... = k" using \<open>k > 0\<close> by simp
  finally have "bit_length lo \<le> k" .

  with le_add_diff_inverse have lloz: "length (?lo @ ?zs) = k"
    unfolding length_append length_replicate .

  have "?n (?lo @ ?zs @ ?up) = ?n ((?lo @ ?zs) @ ?up)" unfolding append_assoc ..
  also have "... = up * 2 ^ length (?lo @ ?zs) + lo" unfolding nat_of_bin_app by simp
  also have "... = ?lhs" unfolding lloz ..
  finally show ?thesis by (rule sym)
qed (* cases "up = 0" and "lo = 0" by *) (simp_all add: nat_of_bin_app_0s)

corollary add_suffix_bin':
  fixes up lo k :: nat
  assumes "up > 0" (* required to prevent leading zeroes *)
    and "lo < 2^k"
  shows "bin_of_nat (up * 2^k + lo) = (bin_of_nat lo) @ (replicate (k - (length (bin_of_nat lo))) False) @ (bin_of_nat up)"
    (is "?lhs = ?lo @ ?zs @ ?up")
proof -
  from \<open>up > 0\<close> have "ends_in True ?up" unfolding bin_of_nat_end_True .
  moreover from bin_of_nat_len_gt_0 and \<open>up > 0\<close> have "?up \<noteq> []" by simp
  ultimately have "ends_in True (?lo @ ?zs @ ?up)" unfolding ends_in_append by simp

  with bin_nat_bin[symmetric] have "?lo @ ?zs @ ?up = bin_of_nat (nat_of_bin (?lo @ ?zs @ ?up))" .
  also have "... = ?lhs" using add_suffix_bin[of lo k up] assms by presburger
  finally show ?thesis by (rule sym)
qed

lemma suffix_len_eq:
  fixes up lo k :: nat
  assumes "up > 0"
    and "lo < 2^k"
  defines "n' \<equiv> up * 2^k"
  defines "n \<equiv> n' + lo"
  shows "bit_length n' = bit_length n" (is "?l n' = ?l n")
proof (cases "lo > 0")
  assume "lo > 0"
  have "k > 0" proof (rule ccontr)
    assume "\<not> 0 < k"
    then have "k = 0" by simp
    with \<open>lo < 2^k\<close> have "lo = 0" by simp
    with \<open>lo > 0\<close> show False by simp
  qed

  let ?up = "bin_of_nat up" and ?lo = "bin_of_nat lo"
    and ?z = "\<lambda>k. replicate k False" and ?lb = "\<lambda>n. length (bin_of_nat n)"

  from \<open>up > 0\<close> have "n' > 0" unfolding n'_def by simp
  then have "n > 0" unfolding n_def by simp

  from n'_def have n'_eq: "n' = up * 2^k + 0" by simp

  from \<open>lo < 2^k\<close> have "lo \<le> 2^k - 1" by simp
  with log_mono have "dlog lo \<le> dlog (2^k - 1)" ..

  have "?lb lo = dlog lo + 1" using \<open>lo > 0\<close> by (rule bit_len_eq_dlog)
  also have "... \<le> dlog (2^k - 1) + 1" using \<open>dlog lo \<le> dlog (2^k - 1)\<close> by (rule add_right_mono)
  also have "... = k" unfolding log_exp_m1 using \<open>k > 0\<close> by (subst le_add_diff_inverse2) force+
  finally have "?lb lo \<le> k" .

  have "bin_of_nat n' = ?z k @ ?up" unfolding n'_eq using add_suffix_bin'[of up 0 k] \<open>up > 0\<close> zero_less_power pos2 by simp
  with arg_cong have "?lb n' = length (?z k @ ?up)" .
  also have "... = length (?lo @ ?z (k - ?lb lo) @ ?up)"
    unfolding length_append length_replicate add.assoc[symmetric] \<open>k \<ge> ?lb lo\<close>[THEN le_add_diff_inverse] ..
  also have "... = ?lb n"
  proof (rule arg_cong[where f=length], rule sym)
    show "bin_of_nat n = ?lo @ ?z (k - ?lb lo) @ ?up" unfolding n_def n'_def using add_suffix_bin' \<open>up > 0\<close> \<open>lo < 2^k\<close> .
  qed
  finally show "?lb n' = ?lb n" .
qed (* case "lo = 0" by *) (simp add: assms)


lemma bin_prefix_add:
  assumes "up > 0"
    and "lo < 2^k"
  shows "bin_prefix (bin_of_nat up) (up * 2^k + lo)"
  unfolding bin_prefix_def using add_suffix_bin'[folded append_assoc] and assms
  by (intro suffixI)

corollary bin_prefix_zs:
  assumes "up > 0"
  shows "bin_prefix (bin_of_nat up) (up * 2^k)"
  using bin_prefix_add[where lo = 0] assms by simp

lemma less_imp_add1_le: "a < b \<Longrightarrow> a + 1 \<le> b" for a b :: nat by simp


lemma adj_sq_shared_prefix_half:
  assumes n_len: "bit_length n \<ge> 9" (* lower bound for "4 + l div 2 < l" *)
  defines "k \<equiv> 4 + bit_length n div 2"
  defines "l \<equiv> bit_length n - k"
  defines "sq \<equiv> adj_square n"
  shows "shared_bin_prefix l n sq"
proof (intro shared_bin_prefixI)
  let ?n = "bin_of_nat n"
  define ps where "ps \<equiv> drop k ?n"
  show "bin_prefix ps n" unfolding bin_prefix_def ps_def using suffix_drop .
  show "length ps = l" unfolding ps_def k_def length_drop l_def ..

  have "n > 0" (* why is the short form not working here? *)
  proof (rule ccontr)
    show "\<not> 0 < n \<Longrightarrow> False" using n_len by simp
  qed

  define up where "up = nat_of_bin ps"
  define lo where "lo = n mod 2^k"
  define n' where "n' = n - lo"
  let ?lo = "bin_of_nat lo" and ?up = "bin_of_nat up"

  have n'_eq: "n' = up * 2^k" unfolding up_def ps_def n'_def lo_def unfolding nat_of_bin_drop nat_bin_nat
    by (rule minus_mod_eq_div_mult)
  have n_eq: "n = up * 2^k + lo" by (fold n'_eq, unfold lo_def n'_def, simp)

  have "k < bit_length n" unfolding k_def using n_len by linarith
  have "ends_in True ?n" using \<open>n > 0\<close> by simp
  with ends_in_drop \<open>k < bit_length n\<close> have "ends_in True ps" unfolding ps_def .
  then have ps_eq: "ps = ?up" unfolding up_def by simp

  define sq_diff where "sq_diff = sq - n'"
  have sq_eq: "sq = next_square n'"
    unfolding sq_def adj_square_def suffix_len_def unfolding n'_def lo_def k_def ..
  have sq_split: "sq = up * 2^k + sq_diff"
    unfolding sq_diff_def n'_eq[symmetric] sq_eq using next_sq_correct2 by force

  note suffix_len_eq
  moreover have "up > 0" proof -
    from \<open>bit_length n > k\<close> have "length ?n - 1 \<ge> k" by simp
    then have "(2::nat)^k \<le> 2^(length ?n - 1)" by simp
    also have "... \<le> n" using nat_of_bin_min[of ?n] \<open>n > 0\<close>
      unfolding nat_bin_nat bin_of_nat_end_True .
    finally have "n \<ge> 2^k" .

    have "(1::nat) = 2^k div 2^k" by simp
    also have "... \<le> n div 2^k" using div_le_mono \<open>n \<ge> 2^k\<close> .
    also have "... = up" unfolding ps_def up_def using nat_of_bin_drop by simp
    finally show "up > 0" by simp
  qed
  moreover have "lo < 2 ^ k" unfolding lo_def using pos_mod_bound zero_less_power pos2 .
  ultimately have l_eq': "bit_length n' = bit_length n" unfolding n'_eq n_eq .

  note bin_prefix_add[of up sq_diff k] and \<open>up > 0\<close>
  moreover have "sq_diff < 2 ^ (4 + bit_length n' div 2)" unfolding sq_diff_def sq_eq using next_sq_diff .
  ultimately show "bin_prefix ps sq" unfolding ps_eq sq_split k_def l_eq' .
qed

lemma suffix_drop_le: "a \<ge> b \<Longrightarrow> suffix (drop a xs) (drop b xs)"
proof -
  assume "a \<ge> b"
  then have *: "drop a xs = drop (a - b) (drop b xs)" by simp
  show ?thesis unfolding * by (rule suffix_drop)
qed

lemma shared_prefix_len:
  assumes ab: "shared_bin_prefix l1 a b"
    and ls: "l1 \<ge> l2"
  shows "shared_bin_prefix l2 a b"
proof (intro shared_bin_prefixI')
  define psa1 where "psa1 = drop (bit_length a - l1) (bin_of_nat a)"
  define psa2 where "psa2 = drop (bit_length a - l2) (bin_of_nat a)"
  from ab have "length psa1 = l1" unfolding psa1_def ..
  from ab have psa1b: "bin_prefix psa1 b" unfolding psa1_def ..

  from shared_bin_max_len1 ab have "l1 \<le> bit_length a" .
  with le_trans ls show "l2 \<le> bit_length a" .

  from \<open>l1 \<ge> l2\<close> have "bit_length a - l1 \<le> bit_length a - l2" by (rule diff_le_mono2)
  then have "suffix psa2 psa1" unfolding psa1_def psa2_def by (rule suffix_drop_le)

  with suffix_order.order_trans show "bin_prefix psa2 b" using psa1b unfolding bin_prefix_def .
qed

lemma shared_prefix_log_ineq: "l \<ge> 18 \<Longrightarrow> dlog l \<le> l div 2 - 5"
proof (induction l rule: nat_induct_at_least)
  case base (* l = 18 *)
  show ?case by (simp add: Discrete.log.simps)
next
  case (Suc n)
  let ?Sn = "Suc n"
  from \<open>n \<ge> 18\<close> have "n \<noteq> 0" "n > 0" by linarith+
  from dlog_Suc \<open>n > 0\<close> have dlog_Suc': "dlog ?Sn = (if ?Sn = 2 ^ dlog ?Sn then Suc (dlog n) else dlog n)" .

  note remove_plus1 = nat.inject[unfolded Suc_eq_plus1] Suc_le_mono[unfolded Suc_eq_plus1]

  show ?case proof (cases "?Sn = 2 ^ dlog ?Sn")
    case True
    then have "even ?Sn" using dlog_Suc' by fastforce
    then have div_eq: "?Sn div 2 = n div 2 + 1" by simp

    from True have "dlog ?Sn = (dlog n) + 1" by (subst dlog_Suc') simp
    also have "... \<le> n div 2 - 5 + 1" unfolding remove_plus1 using Suc.IH .
    also have "... = n div 2 + 1 - 5" using \<open>n \<ge> 18\<close> by (intro add_diff_assoc2) linarith
    also have "... = ?Sn div 2 - 5" unfolding div_eq ..
    finally show ?thesis .
  next
    case False
    then have "dlog ?Sn = dlog n" by (subst dlog_Suc') simp
    also have "... \<le> n div 2 - 5" unfolding remove_plus1 using Suc.IH .
    also have "... \<le> ?Sn div 2 - 5" by (intro diff_le_mono) (rule Suc_div_le_mono)
    finally show ?thesis .
  qed
qed

lemma int_nat_le: "int x \<le> y \<Longrightarrow> x \<le> nat y"
proof -
  assume "int x \<le> y"
  then have "nat (int x) \<le> nat y" by (rule nat_mono)
  then show "x \<le> nat y" unfolding nat_int .
qed

theorem adj_sq_shared_prefix_log:
  fixes n
  assumes "bit_length n \<ge> 18" (* lower bound for "dlog l + 1 \<le> l div 2 - 4" *)
  defines "l \<equiv> nat \<lceil>log 2 (bit_length n)\<rceil>"
  defines "sq \<equiv> adj_square n"
  shows "shared_bin_prefix l n sq"
    (is "?sp l n sq")
proof -
  define bln where "bln = bit_length n"
  let ?lh = "bln - (4 + bln div 2)"
  have "bln \<ge> 18" unfolding bln_def using \<open>bit_length n \<ge> 18\<close> .

  from \<open>bln \<ge> 18\<close> have "bln \<ge> 9" by simp
  then have sp_lh: "?sp ?lh n sq" unfolding sq_def bln_def by (intro adj_sq_shared_prefix_half)

  have "l \<le> nat \<lfloor>log 2 bln\<rfloor> + 1" unfolding l_def bln_def using ceil_le_floor_plus1_nat .
  also have "... = dlog bln + 1" unfolding log_altdef using \<open>bln \<ge> 9\<close> by presburger
  also have "... \<le> bln div 2 - 4"
  proof -
    from \<open>bln \<ge> 18\<close> have h1: "a \<le> bln div 2 - 4 - 1 \<longleftrightarrow> a + 1 \<le> bln div 2 - 4" for a
      by (intro le_diff_conv2 add_le_imp_le_diff) linarith

    from shared_prefix_log_ineq \<open>bln \<ge> 18\<close> have "dlog bln \<le> bln div 2 - 5" .
    also have "... = bln div 2 - 4 - 1" by fastforce

    finally show ?thesis unfolding h1 .
  qed

  also have "... = bln div 2 * 2 - bln div 2 - 4" unfolding mult_2_right by simp
  also have "... \<le> bln - bln div 2 - 4" by (intro diff_le_mono) (rule div_times_less_eq_dividend)
  also have "... = bln - (4 + bln div 2)" unfolding diff_diff_left by presburger
  finally have "l \<le> ?lh" .
  with shared_prefix_len sp_lh show "?sp l n sq" .
qed

corollary adj_sq_shared_prefix_log':
  fixes n
  assumes "bit_length n \<ge> 18"
  defines "l \<equiv> nat \<lceil>log 2 (bit_length n)\<rceil>"
  obtains w where "w \<in> SQ"
    and "shared_bin_prefix l n (gn w)"
proof
  let ?sq = "adj_square n" let ?w = "gn_inv ?sq"

  have "?sq > 0" unfolding adj_square_def using next_sq_gt0 .
  then have gn_nat: "gn ?w = ?sq" by (rule inv_gn_id)

  show "?w \<in> SQ" using adj_sq_correct' .
  show "shared_bin_prefix l n (gn ?w)" unfolding l_def \<open>gn ?w = ?sq\<close>
    using adj_sq_shared_prefix_log \<open>bit_length n \<ge> 18\<close> .
qed


end
