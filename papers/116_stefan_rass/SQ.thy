theory SQ
  imports Complex_Main gn dens "HOL-Library.Discrete" "HOL-Library.Sublist"
begin

subsection\<open>Language of integer squares\<close>

(* SQ is an overloaded identifier in the paper *)
definition SQ :: lang \<comment> \<open>then language of non-zero square numbers, represented by binary string without leading ones\<close>
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
  shows SQ_nat_vim: "SQ = nat_of_num -` SQ_nat"
    and SQ_nat_eq: "SQ = {w. nat_of_num w \<in> SQ_nat}"
  by (simp_all add: nat_of_num_pos)

lemma SQ_nat_im: "SQ_nat = gn ` SQ"
proof (intro subset_antisym subsetI) (* equivalent but less straightforward: (intro set_eqI iffI) *)
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
      using SQ_def by simp
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

  have "inj_on gn_inv (power2 ` {0<..Discrete.sqrt x})"
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
  case True show ?thesis
  proof (cases "is_square n")
    case True
    with next_sq_eq[of n] and \<open>n > 0\<close> show ?thesis by (intro eq_imp_le) (rule sym)
  next
    case False
    with next_sq_gt[of n] and \<open>n > 0\<close> show ?thesis by (intro less_imp_le_nat)
  qed
qed (* case "n = 0" by *) simp


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


lemma sqrt_altdef: "Discrete.sqrt n = \<lfloor>sqrt n\<rfloor>"
proof -
  have *: "n = (sqrt n)\<^sup>2" by (subst real_sqrt_pow2) simp_all

  have "(Discrete.sqrt n)\<^sup>2 \<le> n" by simp
  with * have "(Discrete.sqrt n)\<^sup>2 \<le> (sqrt n)\<^sup>2" by simp
  then have upper: "Discrete.sqrt n \<le> sqrt n" by (simp add: real_le_rsqrt)

  have "n < (Discrete.sqrt n + 1)\<^sup>2" using Suc_sqrt_power2_gt by simp
  with * have "(sqrt n)\<^sup>2 < (Discrete.sqrt n + 1)\<^sup>2" by linarith
  then have "(sqrt n)\<^sup>2 < (real (Discrete.sqrt n + 1))\<^sup>2" by simp
  then have lower: "sqrt n < Discrete.sqrt n + 1"
    using power2_less_imp_less[of "sqrt n" "Discrete.sqrt n + 1"] by simp

  from upper and lower show ?thesis by linarith
qed

corollary sqrt_altdef2: "Discrete.sqrt n = nat \<lfloor>sqrt n\<rfloor>" 
  using arg_cong[OF sqrt_altdef, of nat] unfolding nat_int .

lemma sqrt_ceil_floor:
  fixes n :: nat
  assumes "n > 0"
  shows "\<lceil>sqrt n\<rceil> = \<lfloor>sqrt (n - 1)\<rfloor> + 1"
proof -
  let ?dsr = Discrete.sqrt
  have h0: "Suc (n - 1) = n" using \<open>n > 0\<close> by simp
  have h1: "?dsr n = (if is_square n then ?dsr (n - 1) + 1 else ?dsr (n - 1))"
    using sqrt_Suc[of "n - 1"] unfolding h0 unfolding Suc_eq_plus1 .

  have "\<lfloor>sqrt (n - 1)\<rfloor> + 1 - 1 = \<lfloor>sqrt (n - 1)\<rfloor>" by simp
  also have "... \<le> sqrt (n - 1)" by simp
  also have "... < sqrt n" using \<open>n > 0\<close> by simp
  finally have "of_int (\<lfloor>sqrt (n - 1)\<rfloor> + 1) - 1 < sqrt n" by simp
  then have upper: "\<lfloor>sqrt (n - 1)\<rfloor> + 1 \<le> \<lceil>sqrt n\<rceil>" by (subst le_ceiling_iff)

  have "sqrt n \<le> Discrete.sqrt (n - 1) + 1"
  proof (cases "is_square n")
    case True
    then have "Discrete.sqrt (n - 1) + 1 = Discrete.sqrt n" using h1 by presburger
    also have "... = sqrt n" using \<open>is_square n\<close> by auto
    finally show "sqrt n \<le> Discrete.sqrt (n - 1) + 1" by argo
  next
    case False
    then have "Discrete.sqrt (n - 1) + 1 = Discrete.sqrt n + 1" using h1 by presburger
    also have "... = \<lfloor>sqrt n\<rfloor> + 1" by (simp add: sqrt_altdef)
    also have "... > sqrt n" by simp
    finally show "sqrt n \<le> Discrete.sqrt (n - 1) + 1" by simp
  qed
  moreover have "Discrete.sqrt (n - 1) + 1 = \<lfloor>sqrt (n - 1)\<rfloor> + 1" using sqrt_altdef by simp
  ultimately have "sqrt n \<le> \<lfloor>sqrt (n - 1)\<rfloor> + 1" by auto
  then have lower: "\<lceil>sqrt n\<rceil> \<le> \<lfloor>sqrt (n - 1)\<rfloor> + 1" by (subst ceiling_le_iff)

  from lower and upper show ?thesis by (rule antisym)
qed

lemma next_sq_correct3: "n > 0 \<Longrightarrow> next_square n = \<lceil>sqrt n\<rceil>\<^sup>2"
  using sqrt_ceil_floor sqrt_altdef by simp


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

  from le2 have "\<lceil>log 2 (2*\<lceil>sqrt x\<rceil>+1)\<rceil> \<le> \<lceil>log 2 (3*\<lceil>sqrt x\<rceil>)\<rceil>"
    by (smt (verit, del_insts) ceiling_mono log_le_cancel_iff of_int_le_1_iff of_int_le_iff)
  also have "\<dots> = \<lceil>(log 2 3) + log 2 \<lceil>sqrt x\<rceil>\<rceil>" using le2 and log_mult[of 2 3 "\<lceil>sqrt x\<rceil>"] by auto
  also have "\<dots> \<le> \<lceil>2 + log 2 \<lceil>sqrt x\<rceil>\<rceil>" using le3 ceiling_mono by (simp add: ceiling_mono)
  also have "\<dots> = 2 + \<lceil>log 2 \<lceil>sqrt x\<rceil>\<rceil>" by linarith
  also have "\<dots> \<le> 2 + \<lceil>\<lceil>log 2 (sqrt x)\<rceil>\<rceil>" using log_ceil_le by (simp add: assms ceiling_le_iff)
  also have "\<dots> = 2 + \<lceil>log 2 (sqrt x)\<rceil>" by simp
  also have "\<dots> = 2 + \<lceil>(log 2 x) / 2\<rceil>" unfolding le4 by (rule refl)
  also have "\<dots> \<le> 3 + \<lceil>log 2 x\<rceil> / 2" using le1 by linarith
  finally show ?thesis by simp
qed


subsection\<open>Log and bit-length\<close>

lemma bit_length_eq_discrete_log:
  "bit_length n = Discrete.log n + 1" (is "?len n = ?log n + 1")
proof (cases "n > 0")
  case True thus ?thesis
  proof (induction n rule: log_induct)
    case (double n)
    have "n = 2 * (n div 2) \<or> n = 2 * (n div 2) + 1" by linarith
    then have "?len n = ?len (2 * (n div 2))" by (standard, simp, presburger add: bit_len_even_odd)
    also have "... = ?len (n div 2) + 1" using bit_len_double and \<open>n \<ge> 2\<close> by auto
    also have "... = ?log (n div 2) + 1 + 1" unfolding double.IH ..
    also have "... = ?log (n) + 1" using log_rec[of n] and \<open>n \<ge> 2\<close> by presburger
    finally show ?case .
  qed (* case "n = 1" by *) force
qed (* case "n = 0" by *) simp

lemma bit_length_eq_log:
  assumes "n > 0"
  shows "bit_length n = \<lfloor>log 2 n\<rfloor> + 1"
  using assms log_altdef bit_length_eq_discrete_log by auto

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

lemma delta_bitlength2:
  "bit_length (next_square n - n) \<le> 3 + (bit_length n) div 2"
  (is "bit_length ?delta \<le> 3 + (bit_length n) div 2")
proof (cases "n > 0", cases "?delta > 0")
  assume "n > 0" and "?delta > 0"

  have "bit_length ?delta = \<lfloor>log 2 ?delta\<rfloor> + 1" using bit_length_eq_log and \<open>?delta > 0\<close> .
  also have "... \<le> \<lfloor>log 2 (2 * Discrete.sqrt n + 1)\<rfloor> + 1"
  proof -
    have "real ?delta \<le> real (2 * Discrete.sqrt n + 1)" using next_sq_diff of_nat_le_iff by blast
    then have "log 2 ?delta \<le> log 2 (2 * Discrete.sqrt n + 1)" using \<open>?delta > 0\<close> by (subst log_le_cancel_iff) simp_all
    then have "\<lfloor>log 2 ?delta\<rfloor> \<le> \<lfloor>log 2 (2 * Discrete.sqrt n + 1)\<rfloor>" by (rule floor_mono)
    then show ?thesis by presburger
  qed
  also have "... = \<lfloor>log 2 (2 * \<lfloor>sqrt n\<rfloor> + 1)\<rfloor> + 1"
  proof -
    have "real (2 * Discrete.sqrt n + 1) = real_of_int (2 * \<lfloor>sqrt n\<rfloor> + 1)" by (fold sqrt_altdef) simp
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
        then have "n = \<lfloor>sqrt n\<rfloor>\<^sup>2" using real_sqrt_pow2
          by (metis floor_of_int floor_of_nat of_nat_0_le_iff)
        then have "n = (nat \<lfloor>sqrt n\<rfloor>)\<^sup>2"
          by (metis nat_int of_nat_power sqrt_altdef)
        then have "is_square n" ..
        then have "next_square n = n" using next_sq_eq and \<open>n > 0\<close> by blast
        then show False using \<open>?delta > 0\<close> by simp
      qed
    qed
    then show "?l + 1 \<le> ?r" by simp
  qed
  also have "... \<le> 3 + \<lceil>log 2 n\<rceil> div 2" using delta_bitlength and \<open>n > 0\<close>
  proof -
    have "\<lceil>log 2 (2 * \<lceil>sqrt n\<rceil> + 1)\<rceil> = \<lfloor> \<lceil>log 2 (2 * \<lceil>sqrt n\<rceil> + 1)\<rceil> \<rfloor>" using floor_of_int by simp
    also have "... \<le> \<lfloor>3 + \<lceil>log 2 n\<rceil> / 2\<rfloor>" using delta_bitlength[of n] and \<open>n > 0\<close> by linarith
    also have "... = 3 + \<lceil>log 2 n\<rceil> div 2" by linarith
    finally show ?thesis .
  qed
  also have "... \<le> 3 + (\<lfloor>log 2 n\<rfloor> + 1) div 2" using ceil_le_floor_plus1[of "log 2 n"] by simp
  also have "... = 3 + bit_length n div 2" using bit_length_eq_log[of n] and \<open>n > 0\<close> by simp
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
 * simplest fix: when this happens, use prev_square n := (Discrete.sqrt n)²
 *)

abbreviation dlog :: "nat \<Rightarrow> nat" 
  where "dlog \<equiv> Discrete.log"

abbreviation dsqrt :: "nat \<Rightarrow> nat"
  where "dsqrt \<equiv> Discrete.sqrt"

abbreviation prev_square :: "nat \<Rightarrow> nat"
  where "prev_square n \<equiv> (dsqrt n)\<^sup>2"

(* maybe the bit_length is easier to work with than the discrete log *)
definition adj_square :: "nat \<Rightarrow> nat" (*adjacent square*)
  where "adj_square n = (if dlog n = dlog (next_square n) then next_square n else prev_square n)"

declare adj_square_def[simp]

lemma shared_prefix:
(*
 \<open>n\<close> and \<open>adj_square n\<close> share a common prefix \<open>ps\<close> with a min length of \<open>\<lceil>log 2 (bit_length n)\<rceil>.\<close>
 The universal TM on input \<open>w\<close> only cares about the most \<open>\<lceil>log 2 w\<rceil>\<close> bits.
 Thus using \<open>adj_square n\<close> instead of \<open>n\<close> does not change the computation.
*)
  assumes "bit_length n \<ge> 9"
  obtains ps
  where "suffix ps (bin_of_nat n)"
    and "suffix ps (bin_of_nat (adj_square n))"
    and "length ps \<ge> \<lceil>log 2 (bit_length n)\<rceil>"
  sorry

end
