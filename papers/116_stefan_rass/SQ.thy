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

(* prove correctness of the shortcut (is this necessary?) *)
lemma
  assumes "n > 0"
  shows "log2 n = floor (log 2 n) + 1"
proof -
  (* try to follow https://math.stackexchange.com/a/3550303/870587 *)

  let ?b = "bin_of_nat n" let ?nbn = "nat_of_bin ?b"
  let ?d = "length ?b" (* number of digits *)

  (* step 1: bounds on n *)

  (* helper for bounds *)
  from powr_realpow[of 2] have realpow2: "2 powr x = 2 ^ x" for x by simp

  (* lower bound: n \<ge> 2^(d-1) *)
  from \<open>n > 0\<close> have "ends_in True ?b" using bin_of_nat_end_True by simp
  then have "2 ^ (?d - 1) \<le> ?nbn" by (rule nat_of_bin_min[of ?b])
  then have "2 ^ (?d - 1) \<le> n" unfolding nat_bin_nat[of n] .
  then have "2 powr (?d - 1) \<le> n" unfolding realpow2 by simp

  (* upper bound: n \<le> 2^d - 1 *)
  from nat_of_bin_max[of ?b] have "n < 2 ^ ?d" unfolding nat_bin_nat .
  then have "n + 1 \<le> 2 ^ ?d" by linarith
  then have "n + 1 \<le> 2 powr ?d" unfolding realpow2 using of_nat_le_numeral_power_cancel_iff by blast 
  then have "n \<le> 2 powr ?d - 1" by linarith
  
  (* probably irrelevant:
  (* lower bound: n \<ge> 2 ^ (d-1) *)
  from \<open>n > 0\<close> have "n = 2 powr (log 2 n)" using powr_log_cancel[of 2 n] by auto
  then have "n \<ge> 2 powr (floor (log 2 n))" by (metis of_int_floor_le powr_mono one_le_numeral)
  then have "n \<ge> 2 powr (?d - 1)" by simp
  (* upper bound: n < 2 ^ d *)
  have "n < 2 powr (floor (log 2 n) + 1)" by (simp add: assms less_powr_iff)
   *)

  find_theorems "_ powr _"

  (* may be helpful *)
  thm floor_log2_div2
  thm powr_log_cancel
  thm powr_realpow
  thm log_less_cancel_iff (* log_mono *)
  thm less_imp_of_nat_less (* real_mono *)
  thm floor_Fract

  oops

end