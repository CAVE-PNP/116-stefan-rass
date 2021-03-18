theory SQ
  imports Complex_Main gn dens "HOL-Library.Discrete"
begin

term "Discrete.log"
find_theorems "Discrete.log" "log"

(* TODO review this (StefanH, StefanR)
 * SQ is an overloaded identifier in the paper. 
 *)
definition SQ :: lang where \<comment> \<open>the \<^emph>\<open>language\<close> \<open>SQ \<subseteq> \<Sigma>\<^sup>*\<close>, as defined in ch 4.4\<close>
  "SQ \<equiv> {w. \<exists>x. nat_of_bin w = x ^ 2}"

definition SQ' :: lang where \<comment> \<open>modified version of \<open>SQ\<close> for which the following is easier to show\<close>
  "SQ' \<equiv> {w. \<exists>x. gn w = x ^ 2}"

definition SQ_nat :: "nat set" where \<comment> \<open>the analogous set \<open>SQ \<subseteq> \<nat>\<close>, as defined in ch 4.1\<close>
  "(SQ_nat::nat set) \<equiv> {y. \<exists>x. y = x ^ 2}"

declare SQ_def[simp] SQ'_def[simp] SQ_nat_def[simp]

(* relating SQ, SQ', and SQ_nat *)
lemma SQ_SQ_nat:
  shows SQ_nat_vim: "SQ = nat_of_bin -` SQ_nat"
    and SQ_nat_eq: "SQ = {w. nat_of_bin w \<in> SQ_nat}"
    and SQ'_nat_vim: "SQ' = gn -` SQ_nat"
    and SQ'_nat_eq: "SQ' = {w. gn w \<in> SQ_nat}"
  by simp_all

lemma SQ_nat_im: "SQ_nat = nat_of_bin ` SQ" 
  using SQ_nat_vim
  by (metis image_eqI image_vimage_subset mem_Collect_eq nat_bin_nat subsetI subset_antisym vimage_def)

lemma SQ'_nat_im: "SQ_nat = gn ` SQ' \<union> {0}"
proof (standard; standard)
  fix n
  assume a: "n \<in> SQ_nat"
  then show "n \<in> gn ` SQ' \<union> {0}"
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc nat)
    from \<open>n \<in> SQ_nat\<close> obtain x where b: "n = x ^ 2" by force
    with Suc have c: "gn (gn_inv n) = x ^ 2" using inv_gn_id by (metis is_gn.simps zero_less_Suc)
    then have "n \<in> {n. \<exists>x. gn (gn_inv n) = x ^ 2}" by force
    then have "n \<in> gn ` SQ'" by (metis a b c SQ'_nat_eq image_eqI mem_Collect_eq)
    then show ?thesis by simp
  qed
next
  fix n
  assume "n \<in> gn ` SQ' \<union> {0}"
  then have a: "n \<in> gn ` SQ' \<or> n = 0" by blast
  then show "n \<in> SQ_nat"
  proof (cases "n = 0")
    case True thus ?thesis by simp
  next
    case False
    with a have "n \<in> gn ` SQ'" by blast
    then have "n \<in> {n. \<exists>x. gn (gn_inv n) = x ^ 2}" using gn_inv_id by fastforce
    then have "\<exists>x. gn (gn_inv n) = x ^ 2" by blast
    then obtain x where "gn (gn_inv n) = x ^ 2" ..
    
    with False have "n = x ^ 2" using inv_gn_id by simp
    then show ?thesis by simp
  qed
qed

(* floor of log\<^sub>2 n for easier access *)
fun floor_log_2 :: "nat \<Rightarrow> nat" where
  "floor_log_2 n = length (bin_of_nat n) - 1"

(* prove correctness of the shortcut *)
lemma
  assumes "n > 0"
  shows "floor_log_2 n = floor (log 2 n)"
proof -
  (* proof steps from https://math.stackexchange.com/a/3550303/870587 *)

  let ?b = "bin_of_nat n" let ?nbn = "nat_of_bin ?b"
  define d where "d = length ?b" (* number of digits *)

  (* helper for bounds *)
  from powr_realpow[of 2] have realpow2: "2 powr x = 2 ^ x" for x by simp

  have lower: "log 2 n \<ge> d - 1" (* lower bound *)
  proof -
    from \<open>n > 0\<close> have "ends_in True ?b" using bin_of_nat_end_True by simp
    then have "2 ^ (d - 1) \<le> ?nbn" unfolding d_def by (rule nat_of_bin_min[of ?b])
    then have "2 ^ (d - 1) \<le> n" unfolding nat_bin_nat[of n] .
    then have "n \<ge> 2 powr (d - 1)" unfolding realpow2 by simp

    with \<open>n > 0\<close> have "log 2 n \<ge> log 2 (2 powr (d - 1))"
      using log_less_cancel_iff[of 2 "2 powr (d - 1)" n] by fastforce
    then show "log 2 n \<ge> d - 1"  by simp
  qed

  have upper: "log 2 n \<le> log 2 (2 powr d - 1)" (* upper bound *)
  proof -
    from nat_of_bin_max[of ?b] have "n < 2 ^ d" unfolding d_def nat_bin_nat .
    then have "n + 1 \<le> 2 ^ d" by linarith
    then have "n + 1 \<le> 2 powr d" unfolding realpow2 using of_nat_le_numeral_power_cancel_iff by blast 
    then have "n \<le> 2 powr d - 1" by linarith

    with \<open>n > 0\<close> have "log 2 n \<le> log 2 (2 powr d - 1)" by simp (* for some reason this is remarkably easier to solve than the similar one above *)
    then show "log 2 n \<le> log 2 (2 powr d - 1)" .
  qed

  have "d - 1 = floor (log 2 (2 powr d - 1))"
  proof -
    from \<open>n > 0\<close> have "d \<ge> 1" unfolding d_def using bin_of_nat_len not_le_imp_less by blast
    from \<open>d \<ge> 1\<close> have h1: "0 < 2 powr d - 1" by auto

    have "d - 1 = log 2 (2 powr (d - 1))" using powr_log_cancel by simp
    also have "... \<le> log 2 (2 powr d - 1)" using upper and lower by simp
    finally have log_lower: "d - 1 \<le> log 2 (2 powr d - 1)" .

    have "log 2 (2 powr d - 1) < log 2 (2 powr d)"
      using h1 and log_less_cancel_iff[of 2 "2 powr d - 1" "2 powr d"] by simp
    also have "... = d" using powr_log_cancel by simp
    finally have log_upper: "log 2 (2 powr d - 1) < d" .

    from log_lower and log_upper show "d - 1 = floor (log 2 (2 powr d - 1))" by linarith
  qed

  also have "... \<ge> floor (log 2 n)" using upper by linarith
  finally have "d - 1 \<ge> floor (log 2 n)" .

  with lower have "d - 1 = floor (log 2 n)" by linarith
  then show "floor_log_2 n = floor (log 2 n)" unfolding d_def and floor_log_2.simps .
qed

(* show padding function to be unnecessary *)
fun c_pad :: "real \<Rightarrow> real" where
  "c_pad y = (if log 2 y = ceiling (log 2 y) then 1 else 0)"

lemma c_pad_replacement:
  "floor (log 2 y) + 1 = ceiling (log 2 y) + c_pad y"
  by (smt (verit, ccfv_threshold) add.left_neutral c_pad.simps ceiling_altdef floor_of_int of_int_1 of_int_add)

(* arithmetic representation of gn of a binary number *)
lemma gn_arith:
  assumes w\<^sub>y: "w\<^sub>y = bin_of_nat y" and "y > 0"
  shows "gn w\<^sub>y = 2 ^ (floor_log_2 y + 1) + y"
proof -
  have "gn w\<^sub>y = nat_of_bin (w\<^sub>y @ [True])" by (rule gn_bin_eq)
  thm nat_of_bin_app1
  also have "... = 2 ^ length w\<^sub>y + nat_of_bin w\<^sub>y" unfolding nat_of_bin_app1 by simp
  also have "... = 2 ^ length (bin_of_nat y) + y" unfolding w\<^sub>y and nat_bin_nat by (rule refl)
  finally show "gn w\<^sub>y = 2 ^ (floor_log_2 y + 1) + y" using \<open>y > 0\<close> and bin_of_nat_len by simp
qed

lemma gn_arith':
  assumes "y > 0"
  shows "gn' y = 2 ^ (floor_log_2 y + 1) + y"
  using \<open>y > 0\<close> and gn_arith by simp

end