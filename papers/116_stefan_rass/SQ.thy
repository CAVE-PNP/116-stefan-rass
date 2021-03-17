theory SQ
  imports Complex_Main gn dens
begin

definition SQ :: lang where
  "SQ \<equiv> {w. \<exists>x. gn w = x ^ 2}"

definition SQ_nat :: "nat set" where
  "SQ_nat \<equiv> {y. \<exists>x. y = x ^ 2}"

declare SQ_def[simp] SQ_nat_def[simp]

lemma SQ_nat_eq: "SQ = {w. gn w \<in> SQ_nat}" by simp

(* floor of log\<^sub>2 n for easier access *)
fun log2 :: "nat \<Rightarrow> nat" where
  "log2 n = length (bin_of_nat n) - 1"

(* prove correctness of the shortcut *)
lemma
  assumes "n > 0"
  shows "log2 n = floor (log 2 n)"
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
  then show "log2 n = floor (log 2 n)" unfolding d_def and log2.simps .
qed

end